-- Prove2me | Definitions.Def_CohenLeeSongLP_StochCentralPath_Basic
-- name    : CohenLeeSongLP_StochCentralPath_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:49:04.404041+00:00
-- url     : https://prove2.me/theorems/f0768200-b746-4e9a-a90e-a686d14a9c14
-- title:
--   Notation of §3 and the potential $\Phi_\lambda(r)=\sum_i\cosh(\lambda r_i)$ with its gradient and Hessian norm
-- statement:
--   This module fixes the notation of §3 (p. 3:7) and the potential of §4.3 (p. 3:17) of Cohen, Lee and Song. Vectors live in $\mathbb R^n$ and all products, quotients and square roots of vectors are taken coordinatewise.
--
--   1. **Multiplicative approximation.** For $a,b\in\mathbb R^n$ and $\epsilon\in\mathbb R$, $a\approx_\epsilon b$ means $(1-\epsilon)b_i\le a_i\le(1+\epsilon)b_i$ for every $i\in[n]$; for a scalar $t$, $a\approx_\epsilon t$ means $(1-\epsilon)t\le a_i\le(1+\epsilon)t$ for every $i$.
--   2. **Euclidean norm.** $\|v\|_2=\big(\sum_{i=1}^n v_i^2\big)^{1/2}$.
--   3. **Potential.** For $\lambda\in\mathbb R$ and $r\in\mathbb R^n$,
--   $$\Phi_\lambda(r)=\sum_{i=1}^n\cosh(\lambda r_i),\qquad \nabla\Phi_\lambda(r)=\big(\lambda\sinh(\lambda r_i)\big)_{i=1}^n,\qquad \|v\|^2_{\nabla^2\Phi_\lambda(r)}=\sum_{i=1}^n\lambda^2\cosh(\lambda r_i)\,v_i^2 .$$
--   The gradient and the Hessian norm are given in closed form, as the proofs of Lemmas 4.12 and 4.13 compute them (the Hessian of $\Phi_\lambda$ is $\mathrm{diag}(\lambda^2\cosh(\lambda r_i))$).
--
--   The potential measures how far the duality measure $\mu=xs$ is from the central path point $t\mathbf 1$ through $r=\mu/t-1$; it is the quantity whose expectation the stochastic central path method keeps bounded.
--
--   **Formalization Note** Mathlib's default norm on `Fin n → ℝ` is the sup norm, so the Euclidean norm is written out as `norm2`. The sup-norm bounds $\|v\|_\infty\le c$ of the paper are stated coordinatewise in the theorems.
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:7, §3 (notation); p. 3:17, Lemma 4.12 (definition of Φ_λ and ∇Φ_λ)

import Mathlib

namespace CohenLeeSongLP.StochCentralPath

/-- Coordinatewise multiplicative approximation of vectors (§3, p. 3:7):
`ApproxVec ε a b` is `a ≈_ε b`, i.e. `(1 - ε) b_i ≤ a_i ≤ (1 + ε) b_i` for every `i`. -/
def ApproxVec {n : ℕ} (ε : ℝ) (a b : Fin n → ℝ) : Prop :=
  ∀ i, (1 - ε) * b i ≤ a i ∧ a i ≤ (1 + ε) * b i

/-- Approximation of a vector by a scalar (§3, p. 3:7):
`ApproxScalar ε a t` is `a ≈_ε t`, i.e. `(1 - ε) t ≤ a_i ≤ (1 + ε) t` for every `i`. -/
def ApproxScalar {n : ℕ} (ε : ℝ) (a : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ i, (1 - ε) * t ≤ a i ∧ a i ≤ (1 + ε) * t

/-- The Euclidean norm `‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` on `ℝⁿ`. (Mathlib's default norm on
`Fin n → ℝ` is the sup norm, so the Euclidean norm is written out.) -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The potential `Φ_λ(r) = ∑ᵢ cosh(λ rᵢ)` (§4.3, p. 3:17). -/
noncomputable def potential {n : ℕ} (lam : ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ i, Real.cosh (lam * r i)

/-- The gradient `∇Φ_λ(r) = (λ sinh(λ rᵢ))ᵢ` (proof of Lemma 4.12, Part 2, p. 3:17). -/
noncomputable def potentialGrad {n : ℕ} (lam : ℝ) (r : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lam * Real.sinh (lam * r i)

/-- The squared local norm `‖v‖²_{∇²Φ_λ(r)} = ∑ᵢ λ² cosh(λ rᵢ) vᵢ²`; the Hessian of `Φ_λ`
is `diag(λ² cosh(λ rᵢ))` (Lemma 4.12, p. 3:17; proof of Lemma 4.13, p. 3:19). -/
noncomputable def hessNormSq {n : ℕ} (lam : ℝ) (r v : Fin n → ℝ) : ℝ :=
  ∑ i, lam ^ 2 * Real.cosh (lam * r i) * v i ^ 2

end CohenLeeSongLP.StochCentralPath


