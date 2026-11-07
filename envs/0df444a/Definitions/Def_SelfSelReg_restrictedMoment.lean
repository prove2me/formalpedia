-- Prove2me | Definitions.Def_SelfSelReg_restrictedMoment
-- name    : SelfSelReg_restrictedMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:10.712401+00:00
-- url     : https://prove2.me/theorems/781ef521-937b-4e4e-a2a7-2d60a26fb247
-- title:
--   Restricted Hermite moments $\mathsf T^Q_d$, coefficients $a_d$, weights $\lambda_i^{(2r)}$, scaled regressors $a_i$
-- statement:
--   Let $H_d$ be the normalized Hermite tensor $H_d(x)=\frac1{\sqrt{d!}}\mathbb E_{X'}[\mathrm{Re}((x+iX')^{\otimes d})]$, $X'\sim N(0,I_n)$. For a threshold $T$ and a non-empty $Q\subseteq[k]$ the **restricted Hermite moment** is the order-$d$ tensor
--   $$\mathsf T^Q_d=\mathbb E_{X,\xi_Q}\big[H_d(X)\,\mathbf 1\{T\le Y_{\max,Q}\le T+1\}\big],$$
--   an unnormalized expectation over the slice of $Q$ (not a conditional moment). With $\sigma_i^2=1+\|w_i\|_2^2$, $u_i=w_i/\|w_i\|_2$ and $\phi_{\sigma^2}$ the $N(0,\sigma^2)$ density, the paper defines
--   $$a_d(\sigma^2)=\int_T^{T+1}\phi_{\sigma^2}(t)\frac{\mathrm{He}_d(t/\sigma)}{\sigma^d\sqrt{d!}}\,dt,\qquad \lambda_i^{(2r)}=a_{2r}(\sigma_i^2)\|w_i\|_2^{2r},\qquad a_i=\frac{a_{2s+1}(\sigma_i^2)}{a_{2s}(\sigma_i^2)}w_i,$$
--   and the even target matrix $A^{(r)}_Q=\sum_{i\in Q}\lambda_i^{(2r)}u_i^{\otimes r}(u_i^{\otimes r})^\top$ (38).
--
--   These are the quantities of the moment structure theorem (Theorem 5.1): the moments are close to weighted sums of rank-one terms in the regressors, with weights $\lambda_i^{(2r)}$.
--
--   **Formalization Note** $H_d$ is the published `GaussPart.hermiteTensor`, whose entries are $\prod_r\mathrm{He}_{\beta_r}(x_r)/\sqrt{d!}$ for the multi-index $\beta$ of the entry; this equals (13) by Proposition 4.5. $\mathrm{He}_d$ is the probabilists' Hermite polynomial. The threshold $T$ (fixed by Hyperparameters 4.1 in the paper) and the order $s$ are explicit arguments. The expectation is over all of $(X,\xi)$; the integrand depends only on $X,\xi_Q$.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), §5, (16)–(19), p.18 (PDF p.21); (13), p.16 (PDF p.19); Proposition 4.5, p.17 (PDF p.20); (38), p.29 (PDF p.32)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_Tensor

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- **Restricted Hermite moments, coefficients, weights and scaled regressors** (§5, (16)–(19); (38)).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), §5, p.18 (PDF p.21): "We consider the restricted Hermite moments
T^Q_d := E_{X,ξ_Q}[H_d(X) 1{T ≤ Y_max,Q ≤ T + 1}]" (16).

`restrictedMoment w T Q d` is the order-`d` tensor `T^Q_d`, entrywise.

**Formalization Note.** `H_d` is the published normalized Hermite tensor `GaussPart.hermiteTensor`,
with entries `∏_r He_{β_r}(x_r)/√(d!)` (`β` the multi-index of the entry); this is (13),
`H_d(x) = (1/√d!) E_{X′}[Re((x + iX′)^{⊗d})]`, by Proposition 4.5 (p.17). The expectation is over
`(X, ξ)` (all noises); the integrand depends only on `X, ξ_Q`. -/
noncomputable def restrictedMoment {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (Q : Finset (Fin k)) (d : ℕ) : Tensor n d := by
  classical
  exact fun J => ∫ z, GaussPart.hermiteTensor d z.1 J * (if inSlice T w Q z.1 z.2 then 1 else 0)
    ∂(jointLaw n k)

/-- `σ_i² = 1 + ‖w_i‖²`, the variance of `Y_i` (§5, p.18). -/
noncomputable def sigmaSq {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (i : Fin k) : ℝ :=
  1 + ‖w i‖ ^ 2

/-- `u_i = w_i/‖w_i‖₂`, the normalized regressor (§5, p.18). -/
noncomputable def unitReg {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (i : Fin k) :
    EuclideanSpace ℝ (Fin n) :=
  ‖w i‖⁻¹ • w i

/-- The restricted moment coefficient (17), p.18:
`a_d(σ²) = ∫_T^{T+1} φ_{σ²}(t) He_d(t/σ)/(σ^d √d!) dt`, with `φ_{σ²}` the `N(0, σ²)` density.

**Formalization Note.** `He_d(t)/√d!` is `GaussPart.hermiteOne d t` (Mathlib's probabilists'
`Polynomial.hermite`); `φ_{σ²}` is `gaussianPDFReal 0 σ²`. The threshold `T` is an explicit argument
(the paper fixes it by Hyperparameters 4.1). -/
noncomputable def coeff (T : ℝ) (d : ℕ) (σsq : ℝ) : ℝ :=
  ∫ t in T..T + 1, gaussianPDFReal 0 σsq.toNNReal t * GaussPart.hermiteOne d (t / Real.sqrt σsq) /
    Real.sqrt σsq ^ d

/-- The degree-`2r` weight (18), p.18: `λ_i^{(2r)} = a_{2r}(σ_i²) ‖w_i‖₂^{2r}`. -/
noncomputable def weight {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ) (i : Fin k)
    (r : ℕ) : ℝ :=
  coeff T (2 * r) (sigmaSq w i) * ‖w i‖ ^ (2 * r)

/-- The scaled regressor (19), p.18: `a_i = (a_{2s+1}(σ_i²)/a_{2s}(σ_i²)) w_i`. -/
noncomputable def scaledReg {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ) (s : ℕ)
    (i : Fin k) : EuclideanSpace ℝ (Fin n) :=
  (coeff T (2 * s + 1) (sigmaSq w i) / coeff T (2 * s) (sigmaSq w i)) • w i

/-- The even target matrix (38), p.29 (PDF p.32):
`A^{(r)}_Q = Σ_{i∈Q} λ_i^{(2r)} u_i^{⊗r}(u_i^{⊗r})ᵀ`, an `n^r × n^r` matrix. -/
noncomputable def evenTarget {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (Q : Finset (Fin k)) (r : ℕ) : Matrix (Fin r → Fin n) (Fin r → Fin n) ℝ :=
  ∑ i ∈ Q, weight w T i r •
    Matrix.vecMulVec (tensorPow (unitReg w i) r) (tensorPow (unitReg w i) r)

end SelfSelReg


