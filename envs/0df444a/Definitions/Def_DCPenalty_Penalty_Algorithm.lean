-- Prove2me | Definitions.Def_DCPenalty_Penalty_Algorithm
-- name    : DCPenalty_Penalty_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:42.484648+00:00
-- url     : https://prove2.me/theorems/c4022bcf-96c3-407e-bc47-2b2abc3f2b29
-- title:
--   (1.13), (3.1)–(3.5), Algorithm 3.1, pp. 4, 8–9 — the penalty function F_ρ, the ε-active sets, the model Q_ρ and runs of the penalty method
-- statement:
--   For the constrained DC program (1.1), with $[a]_+=\max\{a,0\}$ and an exponent $p\ge 1$, this file defines:
--
--   1. the **penalty function** (1.13): $F_\rho(x)=F(x)+\rho\sum_{i=1}^I[\phi_i(x)+\zeta_i(x)-\psi_i(x)]_+^p$;
--   2. for $\epsilon>0$, the $\epsilon$-active sets (3.1)–(3.2): $\mathcal J_{0,\epsilon}(x)=\{j:\ \psi_0(x)\le\psi_{0,j}(x)+\epsilon\}$ and $\mathcal J_\epsilon(x)=\{\mathbb J:\ \psi_i(x)\le\psi_{i,j_i}(x)+\epsilon\ \forall i\in\mathcal I\}$;
--   3. the quadratic upper model (3.3): $\hat\phi_i(x;\bar x)=\phi_i(\bar x)+\nabla\phi_i(\bar x)^T(x-\bar x)+L_i\|x-\bar x\|^2/2$;
--   4. the convex model of the penalty function (3.5):
--   $$
--   Q_\rho(x;\bar x,j_0,\mathbb J)=\hat\phi_0(x;\bar x)+\zeta_0(x)-\ell_{\psi_{0,j_0}}(x;\bar x)+\rho\sum_{i=1}^I\big[\hat\phi_i(x;\bar x)+\zeta_i(x)-\ell_{\psi_{i,j_i}}(x;\bar x)\big]_+^p;
--   $$
--   5. a **run of Algorithm 3.1**: inputs $\epsilon>0$, $\rho_0>0$, $\sigma>1$ and $\eta_k\ge 0$ with $\eta_k\to 0$; penalty parameters $\rho_k=\rho_0\sigma^k$ (Step 2, $\rho_{k+1}=\sigma\rho_k$); and iterates $x^k\in X$ satisfying (3.7),
--   $$
--   F_{\rho_k}(x^k)\le Q_{\rho_k}(x;x^k,j_0,\mathbb J)+\eta_k\qquad\forall x\in X,
--   $$
--   for every $j_0\in\mathcal J_{0,\epsilon}(x^k)$ and every $\mathbb J\in\mathcal J_\epsilon(x^k)$.
--
--   A run is the object the paper's convergence theorem (Theorem 3.1) is about: any sequence produced by Step 1 of the method, however the approximate subproblem solutions are computed.
--
--   **Formalization Note** $[a]_+^p$ is `(max a 0) ^ p` with real exponent (`Real.rpow`); the base is nonnegative. The run is a predicate on $(p,\epsilon,\rho_0,\sigma,\eta,x)$; it does not assert that runs exist (that is the paper's Theorem 5.1, not formalized). $p\ge 1$ is a condition of the run because the paper fixes it in (1.13) and (3.5) rather than in the input list.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 4, (1.13); p. 8, (3.1), (3.2), (3.3), (3.5); p. 9, Algorithm 3.1, (3.7)

import Mathlib
import Definitions.Def_DCPenalty_Penalty_Problem

namespace DCPenalty.Penalty

open Filter Topology

namespace DCProblem

variable {n m : ℕ} (P : DCProblem n m)

/-- (3.3): `φ̂_i(x; x̄) = φ_i(x̄) + ∇φ_i(x̄)ᵀ(x − x̄) + L_i ‖x − x̄‖² / 2`. -/
noncomputable def phiHat (i : Fin (m + 1)) (xbar x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.φ i xbar + fderiv ℝ (P.φ i) xbar (x - xbar) + P.L i * ‖x - xbar‖ ^ 2 / 2

/-- (3.1): `𝓙_{0,ε}(x) = {j ∈ 𝓙_0 | ψ_0(x) ≤ ψ_{0,j}(x) + ε}`. -/
def J0eps (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Set (Fin (P.J 0)) :=
  {j | P.psi 0 x ≤ P.ψ 0 j x + ε}

/-- (3.2): `𝓙_ε(x) = {(j_1, …, j_I) ∈ 𝓙 | ψ_i(x) ≤ ψ_{i,j_i}(x) + ε, ∀ i ∈ 𝓘}`. -/
def Jeps (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Set ((i : Fin m) → Fin (P.J i.succ)) :=
  {jj | ∀ i, P.psi i.succ x ≤ P.ψ i.succ (jj i) x + ε}

/-- (1.13): the penalty function `F_ρ(x) = F(x) + ρ Σ_{i=1}^I [φ_i(x) + ζ_i(x) − ψ_i(x)]_+^p`. -/
noncomputable def Frho (p ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.F x + ρ * ∑ i : Fin m, (max (P.g i x) 0) ^ p

/-- (3.5): `Q_ρ(x; x̄, j_0, 𝕁) = φ̂_0(x; x̄) + ζ_0(x) − ℓ_{ψ_{0,j_0}}(x; x̄)
  + ρ Σ_{i=1}^I [φ̂_i(x; x̄) + ζ_i(x) − ℓ_{ψ_{i,j_i}}(x; x̄)]_+^p`. -/
noncomputable def Qrho (p ρ : ℝ) (xbar : EuclideanSpace ℝ (Fin n)) (j0 : Fin (P.J 0))
    (jj : (i : Fin m) → Fin (P.J i.succ)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  P.phiHat 0 xbar x + P.ζ 0 x - lin (P.ψ 0 j0) xbar x +
    ρ * ∑ i : Fin m,
      (max (P.phiHat i.succ xbar x + P.ζ i.succ x - lin (P.ψ i.succ (jj i)) xbar x) 0) ^ p

/-- Algorithm 3.1, p. 9: `x` is a run of the penalty method with exponent `p ≥ 1` and inputs
`ε > 0`, `ρ_0 > 0`, `σ > 1`, `η_k ≥ 0`, `η_k → 0`: with `ρ_k = ρ_0 σ^k` (Step 2), every iterate
satisfies `x^k ∈ X` and (3.7), `F_{ρ_k}(x^k) ≤ Q_{ρ_k}(x; x^k, j_0, 𝕁) + η_k` for all `x ∈ X`,
`j_0 ∈ 𝓙_{0,ε}(x^k)` and `𝕁 ∈ 𝓙_ε(x^k)`. -/
def IsPenaltyRun (p ε ρ0 σ : ℝ) (η : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  0 < ε ∧ 0 < ρ0 ∧ 1 < σ ∧ 1 ≤ p ∧ (∀ k, 0 ≤ η k) ∧ Tendsto η atTop (𝓝 0) ∧
    (∀ k, x k ∈ P.X) ∧
    ∀ k, ∀ j0 ∈ P.J0eps ε (x k), ∀ jj ∈ P.Jeps ε (x k), ∀ y ∈ P.X,
      P.Frho p (ρ0 * σ ^ k) (x k) ≤ P.Qrho p (ρ0 * σ ^ k) (x k) j0 jj y + η k

end DCProblem

end DCPenalty.Penalty


