-- Prove2me | Definitions.Def_RobustUncLP_Ellipsoidal_CQP
-- name    : RobustUncLP_Ellipsoidal_CQP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:08:14.280647+00:00
-- url     : https://prove2.me/theorems/a831926d-107b-4512-8a7b-936537287ada
-- title:
--   Appendix, p. 15 — the generic conic quadratic problem (CQP_p) and its dual (CQP_d)
-- statement:
--   A **conic quadratic problem** in the generic form of the Appendix has design vector $z \in \mathbb R^N$ and reads
--   $$e^Tz + \varphi \to \min \quad \text{s.t.}\quad Rz = r,\qquad \|A_\ell z - b_\ell\| \le c_\ell^Tz - d_\ell,\ \ \ell = 0, \dots, k. \tag{CQP$_p$}$$
--   Here $R \in \mathbb R^{p\times N}$, $r \in \mathbb R^p$, $A_\ell \in \mathbb R^{q_\ell \times N}$, $b_\ell \in \mathbb R^{q_\ell}$, $c_\ell, e \in \mathbb R^N$, and $d_\ell, \varphi \in \mathbb R$. Its dual is
--   $$r^T\lambda + \sum_{\ell=0}^k [d_\ell\nu_\ell + b_\ell^T\mu_\ell] + \varphi \to \max \quad \text{s.t.}\quad R^T\lambda + \sum_{\ell=0}^k [\nu_\ell c_\ell + A_\ell^T\mu_\ell] = e,\qquad \|\mu_\ell\| \le \nu_\ell,\ \ \ell = 0, \dots, k, \tag{CQP$_d$}$$
--   with design variables $\lambda \in \mathbb R^p$, $\mu_\ell \in \mathbb R^{q_\ell}$ and $\nu_\ell \in \mathbb R$. This file defines the data, the feasible sets and the objectives of both problems. They are the setting of the duality statement (II) used in the proof of Theorem 3.1.
--
--   **Formalization Note** The page prints the sum in the equality constraint of (CQP$_d$) as $\sum_{\ell=1}^k$, while its objective, $(D_i[x])$ and $(\mathcal C_i)$ all sum from $\ell = 0$. The sum from $\ell = 0$ is the correct dual and is the one formalized. All norms are Euclidean (`euclidNorm`). A dual point is a triple `(λ, μ, ν)`.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, Appendix, p. 15, (CQP_p) and (CQP_d)

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting

namespace RobustUncLP.Ellipsoidal

open Matrix

/-- Data of a generic conic quadratic problem `(CQP_p)`, Appendix, p. 15: design vector
`z ∈ ℝ^N`, `p` linear equations `Rz = r`, and `k + 1` conic constraints
`‖A_ℓ z − b_ℓ‖ ≤ c_ℓᵀz − d_ℓ` (`A_ℓ` has `q ℓ` rows); objective `eᵀz + φ`. -/
structure CQPData (N p k : ℕ) where
  q : Fin (k + 1) → ℕ
  R : Matrix (Fin p) (Fin N) ℝ
  r : Fin p → ℝ
  A : (ℓ : Fin (k + 1)) → Matrix (Fin (q ℓ)) (Fin N) ℝ
  b : (ℓ : Fin (k + 1)) → Fin (q ℓ) → ℝ
  c : Fin (k + 1) → Fin N → ℝ
  d : Fin (k + 1) → ℝ
  e : Fin N → ℝ
  φ : ℝ

namespace CQPData

variable {N p k : ℕ}

/-- Feasible set of `(CQP_p)`. -/
def primalFeas (P : CQPData N p k) : Set (Fin N → ℝ) :=
  {z | P.R *ᵥ z = P.r ∧ ∀ ℓ, euclidNorm (P.A ℓ *ᵥ z - P.b ℓ) ≤ P.c ℓ ⬝ᵥ z - P.d ℓ}

/-- Objective `eᵀz + φ` of `(CQP_p)`. -/
def primalObj (P : CQPData N p k) (z : Fin N → ℝ) : ℝ :=
  P.e ⬝ᵥ z + P.φ

/-- Feasible set of the dual `(CQP_d)`: `w = (λ, μ, ν)` with
`Rᵀλ + ∑_{ℓ=0}^k [ν_ℓ c_ℓ + A_ℓᵀ μ_ℓ] = e` and `‖μ_ℓ‖ ≤ ν_ℓ` for `ℓ = 0, …, k`. -/
def dualFeas (P : CQPData N p k) :
    Set ((Fin p → ℝ) × ((ℓ : Fin (k + 1)) → Fin (P.q ℓ) → ℝ) × (Fin (k + 1) → ℝ)) :=
  {w | P.Rᵀ *ᵥ w.1 + ∑ ℓ, (w.2.2 ℓ • P.c ℓ + (P.A ℓ)ᵀ *ᵥ w.2.1 ℓ) = P.e ∧
    ∀ ℓ, euclidNorm (w.2.1 ℓ) ≤ w.2.2 ℓ}

/-- Objective `rᵀλ + ∑_{ℓ=0}^k [d_ℓ ν_ℓ + b_ℓᵀ μ_ℓ] + φ` of `(CQP_d)`. -/
def dualObj (P : CQPData N p k)
    (w : (Fin p → ℝ) × ((ℓ : Fin (k + 1)) → Fin (P.q ℓ) → ℝ) × (Fin (k + 1) → ℝ)) : ℝ :=
  P.r ⬝ᵥ w.1 + ∑ ℓ, (P.d ℓ * w.2.2 ℓ + P.b ℓ ⬝ᵥ w.2.1 ℓ) + P.φ

end CQPData

end RobustUncLP.Ellipsoidal


