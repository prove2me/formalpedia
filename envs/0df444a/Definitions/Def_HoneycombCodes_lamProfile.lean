-- Prove2me | Definitions.Def_HoneycombCodes_lamProfile
-- name    : HoneycombCodes_lamProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:40.591628+00:00
-- url     : https://prove2.me/theorems/5b2bc5b1-9994-4171-abd2-639783bffe2f
-- title:
--   Collatz–Wielandt certificate $\lambda_\Omega(w)$, effective dimension $D_{eff}(w)$ and the matrix $J_\Omega$
-- statement:
--   Let $\Omega$ be a finite index set and $p=(p_{\omega,\omega'})$ a real matrix of directed weights. For a positive profile $w=(w_\omega)$ put
--
--   $$
--   S_\nu(w)=\sum_{\omega\in\Omega}p_{\omega,\nu}w_\omega,\qquad \lambda_\Omega(w)=\min_{\nu\in\Omega}\frac{S_\nu(w)}{w_\nu},\qquad
--   D_{eff}(w)=\frac{\bigl(\sum_\omega w_\omega\bigr)^2}{\sum_\omega w_\omega^2/D_\omega}.
--   $$
--
--   The symmetric matrix $J_{\omega,\omega'}=\sqrt{p_{\omega,\omega'}p_{\omega',\omega}}$ defines the **retained positive-weight graph**: $\omega\sim\omega'$ iff $\omega\ne\omega'$ and $J_{\omega,\omega'}>0$. Its largest eigenvalue $\lambda_{max}(J)$ is the published `BlockBochner.lamMax`, referenced by this mission.
--
--   **Formalization Note** $\lambda_\Omega$ is `⨅` over the finite index type (for an empty index type Lean's real `⨅` is $0$).
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §3, eq. (16), p.14 (PDF 16); J_Ω: §3, p.14, and §4.4, p.23 (PDF 25)

import Mathlib

set_option autoImplicit false

namespace HoneycombCodes

/-- The directed **Collatz–Wielandt certificate** of a positive profile,
`λ_Ω(w) = min_{ν ∈ Ω} S_ν(w)/w_ν` with `S_ν(w) = Σ_{ω ∈ Ω} p_{ω,ν} w_ω`, Gay, Granha Jeronimo,
Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51),
eq. (16), p.14 (PDF 16); the same quantity appears in Theorem 4.8, p.24.

**Formalization Note.** The minimum over the finite index type is `⨅ ν`; for an empty index type
Lean's real `⨅` is `0`. -/
noncomputable def lamProfile {Ω : Type*} [Fintype Ω] (p : Ω → Ω → ℝ) (w : Ω → ℝ) : ℝ :=
  ⨅ ν : Ω, (∑ ω : Ω, p ω ν * w ω) / w ν

/-- The **blockwise effective dimension** `D_eff(w) = Z_w² / Σ_{ω ∈ Ω} w_ω²/D_ω` with
`Z_w = Σ_ω w_ω`, arXiv:2608.20287v2, eq. (16), p.14 (PDF 16); written `D_Ω(w)` in Theorem 4.8,
p.24. -/
noncomputable def effDim {Ω : Type*} [Fintype Ω] (D : Ω → ℝ) (w : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, w ω) ^ 2 / ∑ ω : Ω, w ω ^ 2 / D ω

/-- The symmetric matrix `J_{ω,ω′} = √(p_{ω,ω′} p_{ω′,ω})`, arXiv:2608.20287v2, §3, p.14
(PDF 16), and §4.4, p.23. -/
noncomputable def symJ {Ω : Type*} (p : Ω → Ω → ℝ) : Matrix Ω Ω ℝ :=
  fun ω ω' => Real.sqrt (p ω ω' * p ω' ω)

/-- The **retained positive-weight graph**: `ω ∼ ω′` iff `ω ≠ ω′` and `J_{ω,ω′} > 0`,
arXiv:2608.20287v2, Corollary 3.2, p.16, and §4.4, p.23. -/
noncomputable def posWeightGraph {Ω : Type*} (p : Ω → Ω → ℝ) : SimpleGraph Ω :=
  SimpleGraph.fromRel (fun ω ω' => 0 < symJ p ω ω')

end HoneycombCodes


