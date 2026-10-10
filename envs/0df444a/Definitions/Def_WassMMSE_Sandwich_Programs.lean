-- Prove2me | Definitions.Def_WassMMSE_Sandwich_Programs
-- name    : WassMMSE_Sandwich_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:18:34.467213+00:00
-- url     : https://prove2.me/theorems/46ed7f7a-4a18-4789-8a96-e4fc5a1b5a6b
-- title:
--   Finite programs (2.2), (3.4) and the sets 𝒮 of (A.5), (A.9), Lemma A.6; ⟨A,B⟩, λ_min, λ_max
-- statement:
--   This file collects the matrix objects that the finite reformulations of the paper use.
--
--   1. **Trace inner product.** $\langle A,B\rangle=\operatorname{Tr}[A^\top B]$ for $A,B\in\mathbb R^{p\times q}$.
--   2. **Extreme eigenvalues.** For a symmetric $A\in\mathbb S^d$ with $d\ge1$, $\lambda_{\min}(A)$ and $\lambda_{\max}(A)$ are its smallest and largest eigenvalues.
--   3. **Covariance Gelbrich set.** For $\widehat\Sigma\in\mathbb S^d_+$ and $\rho\ge0$,
--   $$\mathcal S=\Big\{\Sigma\in\mathbb S^d_+:\ \operatorname{Tr}\big[\Sigma+\widehat\Sigma-2(\widehat\Sigma^{1/2}\Sigma\widehat\Sigma^{1/2})^{1/2}\big]\le\rho^2\Big\},$$
--   the feasible set of (A.5) and (A.9) and the set of Lemma A.6.
--   4. **Program (2.2).** Over $A\in\mathbb R^{n\times m}$ and $\gamma_x,\gamma_w\ge0$ with $\gamma_xI_n-(I_n-AH)^\top(I_n-AH)\succ0$ and $\gamma_wI_m-A^\top A\succ0$, minimize
--   $$\gamma_x(\rho_x^2-\operatorname{Tr}[\widehat\Sigma_x])+\gamma_x^2\big\langle[\gamma_xI_n-(I_n-AH)^\top(I_n-AH)]^{-1},\widehat\Sigma_x\big\rangle+\gamma_w(\rho_w^2-\operatorname{Tr}[\widehat\Sigma_w])+\gamma_w^2\big\langle(\gamma_wI_m-A^\top A)^{-1},\widehat\Sigma_w\big\rangle.$$
--   Its optimal value is the infimum over the feasible triples.
--   5. **Program (3.4).** Over $\Sigma_x\in\mathbb S^n_+$, $\Sigma_w\in\mathbb S^m_{++}$ satisfying $\operatorname{Tr}[\Sigma_x+\widehat\Sigma_x-2(\widehat\Sigma_x^{1/2}\Sigma_x\widehat\Sigma_x^{1/2})^{1/2}]\le\rho_x^2$ and the analogous constraint for $w$, maximize
--   $$\operatorname{Tr}\big[\Sigma_x-\Sigma_xH^\top(H\Sigma_xH^\top+\Sigma_w)^{-1}H\Sigma_x\big].$$
--   Its optimal value is the supremum over the feasible pairs, and a maximizer is a feasible pair whose objective is at least that of every feasible pair.
--
--   Program (2.2) is the finite reformulation of the Gelbrich MMSE problem (Theorem 2.7) and program (3.4) that of the dual problem over normal priors (Theorem 3.5).
--
--   **Formalization Note** The optimal values of (2.2) and (3.4) are `EReal` infima and suprema over the feasible points (so an empty feasible set gives $+\infty$, respectively $-\infty$, as on the page). The matrix inverses are only evaluated at feasible points, where the matrices are positive definite. $\lambda_{\min}$ and $\lambda_{\max}$ are taken over Mathlib's eigenvalues of a Hermitian matrix; at $d=0$ (or for a non-symmetric argument, which never occurs) they are set to $0$, so that a constraint $\Sigma\succeq\lambda_{\min}(\widehat\Sigma)I_0$ is vacuous on $\mathbb R^{0\times0}$. Square roots are the published `psdSqrt`, applied only to positive semidefinite matrices.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 7 (Notation), p. 9 ((2.2)), p. 13 ((3.4)), pp. 39–41 ((A.5), (A.9), Lemma A.6)

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt

open Classical Matrix

namespace WassMMSE.Sandwich

/-- The trace inner product `⟨A, B⟩ = Tr[Aᵀ B]` on `ℝ^{p×q}` (Notation, p. 7). -/
def frob {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℝ) : ℝ := (Aᵀ * B).trace

/-- `λ_min(A)`, the smallest eigenvalue of a symmetric matrix `A ∈ 𝕊^d`. Convention: `0` when `A` is
not symmetric or `d = 0` (then `A ⪰ λ_min(·) I_d` is vacuous on `ℝ^{0×0}`). -/
noncomputable def lamMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : A.IsHermitian ∧ 0 < d then
    Finset.univ.inf' ⟨⟨0, h.2⟩, Finset.mem_univ _⟩ h.1.eigenvalues
  else 0

/-- `λ_max(A)`, the largest eigenvalue of a symmetric matrix `A ∈ 𝕊^d`. Convention: `0` when `A` is
not symmetric or `d = 0`. -/
noncomputable def lamMax {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : A.IsHermitian ∧ 0 < d then
    Finset.univ.sup' ⟨⟨0, h.2⟩, Finset.mem_univ _⟩ h.1.eigenvalues
  else 0

/-- The covariance slice of the Gelbrich ball (Lemma A.6, p. 41; the constraints of (3.4), (A.5),
(A.9)): `𝒮 = {Σ ∈ 𝕊^d_+ : Tr[Σ + Σ̂ − 2(Σ̂^{1/2} Σ Σ̂^{1/2})^{1/2}] ≤ ρ²}`. -/
noncomputable def covGelbrichSet {d : ℕ} (ρ : ℝ) (Sh : Matrix (Fin d) (Fin d) ℝ) :
    Set (Matrix (Fin d) (Fin d) ℝ) :=
  {S | S.PosSemidef ∧
    (S + Sh - (2 : ℝ) • WassersteinDRO.Gelbrich.psdSqrt
      (WassersteinDRO.Gelbrich.psdSqrt Sh * S * WassersteinDRO.Gelbrich.psdSqrt Sh)).trace ≤ ρ ^ 2}

/-- Feasibility in the finite program (2.2), p. 9: `γ_x, γ_w ≥ 0`,
`γ_x I_n − (I_n − AH)ᵀ(I_n − AH) ≻ 0` and `γ_w I_m − AᵀA ≻ 0`. -/
def IsGelbrichProgramFeasible {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin m) ℝ) (γx γw : ℝ) : Prop :=
  0 ≤ γx ∧ 0 ≤ γw ∧
    (γx • (1 : Matrix (Fin n) (Fin n) ℝ) - (1 - A * H)ᵀ * (1 - A * H)).PosDef ∧
    (γw • (1 : Matrix (Fin m) (Fin m) ℝ) - Aᵀ * A).PosDef

/-- The objective of the finite program (2.2), p. 9:
`γ_x(ρ_x² − Tr[Σ̂_x]) + γ_x²⟨[γ_x I_n − (I_n − AH)ᵀ(I_n − AH)]⁻¹, Σ̂_x⟩
 + γ_w(ρ_w² − Tr[Σ̂_w]) + γ_w²⟨(γ_w I_m − AᵀA)⁻¹, Σ̂_w⟩`. -/
noncomputable def gelbrichProgramObjective {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ)
    (Shx : Matrix (Fin n) (Fin n) ℝ) (Shw : Matrix (Fin m) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin m) ℝ) (γx γw : ℝ) : ℝ :=
  γx * (ρx ^ 2 - Shx.trace) +
    γx ^ 2 * frob (γx • (1 : Matrix (Fin n) (Fin n) ℝ) - (1 - A * H)ᵀ * (1 - A * H))⁻¹ Shx +
  γw * (ρw ^ 2 - Shw.trace) +
    γw ^ 2 * frob (γw • (1 : Matrix (Fin m) (Fin m) ℝ) - Aᵀ * A)⁻¹ Shw

/-- The optimal value of the finite program (2.2), p. 9: the infimum of the objective over the
feasible `(A, γ_x, γ_w)`, in `EReal`. -/
noncomputable def gelbrichProgramValue {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ)
    (Shx : Matrix (Fin n) (Fin n) ℝ) (Shw : Matrix (Fin m) (Fin m) ℝ) : EReal :=
  ⨅ (A : Matrix (Fin n) (Fin m) ℝ) (γx : ℝ) (γw : ℝ) (_ : IsGelbrichProgramFeasible H A γx γw),
    (gelbrichProgramObjective H ρx ρw Shx Shw A γx γw : EReal)

/-- Feasibility in the finite program (3.4), p. 13: `Σ_x ∈ 𝕊ⁿ_+`, `Σ_w ∈ 𝕊ᵐ_{++}`, and both Gelbrich
trace constraints `Tr[Σ + Σ̂ − 2(Σ̂^{1/2} Σ Σ̂^{1/2})^{1/2}] ≤ ρ²`. -/
def IsNormalProgramFeasible {n m : ℕ} (ρx ρw : ℝ) (Shx : Matrix (Fin n) (Fin n) ℝ)
    (Shw : Matrix (Fin m) (Fin m) ℝ) (Sx : Matrix (Fin n) (Fin n) ℝ)
    (Sw : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  Sx ∈ covGelbrichSet ρx Shx ∧ Sw ∈ covGelbrichSet ρw Shw ∧ Sw.PosDef

/-- The objective of (3.4), p. 13: `Tr[Σ_x − Σ_x Hᵀ(H Σ_x Hᵀ + Σ_w)⁻¹ H Σ_x]`. -/
noncomputable def normalProgramObjective {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (Sx : Matrix (Fin n) (Fin n) ℝ) (Sw : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  (Sx - Sx * Hᵀ * (H * Sx * Hᵀ + Sw)⁻¹ * H * Sx).trace

/-- The optimal value of (3.4), p. 13: the supremum of the objective over the feasible
`(Σ_x, Σ_w)`, in `EReal` (`⊥` if the feasible set is empty). -/
noncomputable def normalProgramValue {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ)
    (Shx : Matrix (Fin n) (Fin n) ℝ) (Shw : Matrix (Fin m) (Fin m) ℝ) : EReal :=
  ⨆ (Sx : Matrix (Fin n) (Fin n) ℝ) (Sw : Matrix (Fin m) (Fin m) ℝ)
    (_ : IsNormalProgramFeasible ρx ρw Shx Shw Sx Sw), (normalProgramObjective H Sx Sw : EReal)

/-- `(Σ_x, Σ_w)` is a maximizer of (3.4), p. 13: it is feasible and its objective is at least that
of every feasible pair. -/
def IsNormalProgramMaximizer {n m : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) (ρx ρw : ℝ)
    (Shx : Matrix (Fin n) (Fin n) ℝ) (Shw : Matrix (Fin m) (Fin m) ℝ)
    (Sx : Matrix (Fin n) (Fin n) ℝ) (Sw : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  IsNormalProgramFeasible ρx ρw Shx Shw Sx Sw ∧
    ∀ (Sx' : Matrix (Fin n) (Fin n) ℝ) (Sw' : Matrix (Fin m) (Fin m) ℝ),
      IsNormalProgramFeasible ρx ρw Shx Shw Sx' Sw' →
        normalProgramObjective H Sx' Sw' ≤ normalProgramObjective H Sx Sw

end WassMMSE.Sandwich


