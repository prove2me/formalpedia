-- Prove2me | Definitions.Def_GeomQM_MomentumMap_Defs
-- name    : GeomQM_MomentumMap_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:53.010117+00:00
-- url     : https://prove2.me/theorems/b2de2ac1-9c3d-40a0-b5ed-98fb45fd06db
-- title:
--   §2.1–2.2, §3.1–3.2, pp. 4–12 — Lie and Jordan products on Hermitian matrices, f_A, canonical bracket and metric G on ℂⁿ, momentum map µ(ψ) = |ψ⟩⟨ψ|, tensors Λ (11) and R (12)
-- statement:
--   Throughout, $n\in\mathbb N$, $\mathcal H=\mathbb C^n$, and observables are $n\times n$ complex Hermitian matrices. Vectors are $\psi\in\mathbb C^n$, with $\langle\psi|\phi\rangle=\sum_k\overline{\psi_k}\,\phi_k$ (conjugate-linear in the first slot). This module defines the objects of §2.1–2.2 and §3.1–3.2 of the paper.
--
--   1. **The isomorphism (2)**: $\alpha(A)=iA$, from observables to the Lie algebra $\mathfrak u(\mathcal H)$ of anti-Hermitian matrices.
--   2. **The Lie product (3)**: $[A,B]_-=\alpha^{-1}\big(\alpha(A)\alpha(B)-\alpha(B)\alpha(A)\big)=i(AB-BA)$.
--   3. **The Jordan product (6)**: $A\circ B=\tfrac12(AB+BA)$.
--   4. **The scalar product (4)**: $\langle A,B\rangle=\tfrac12\operatorname{Tr}(AB)$, taken as a complex number.
--   5. **The quadratic function of Lemma 5**: $f_A(\psi)=\tfrac12\langle\psi|A\psi\rangle\in\mathbb C$ for any complex matrix $A$; and its real part, which is $f_A$ viewed as a real function on $\mathbb C^n\cong\mathbb R^{2n}$.
--   6. **Real coordinates** $z_k=q_k+ip_k$ (p. 11): for $f:\mathbb C^n\to\mathbb R$, $\partial f/\partial q_k$ is the (real) directional derivative along the $k$-th basis vector $e_k$, and $\partial f/\partial p_k$ the directional derivative along $ie_k$.
--   7. **The canonical Poisson bracket** (p. 12):
--   $$\{f,g\}=\sum_{k=1}^n\Big(\frac{\partial f}{\partial q_k}\frac{\partial g}{\partial p_k}-\frac{\partial f}{\partial p_k}\frac{\partial g}{\partial q_k}\Big).$$
--   8. **The contravariant Euclidean structure** $G=\sum_k\big(\partial_{q_k}\otimes\partial_{q_k}+\partial_{p_k}\otimes\partial_{p_k}\big)$ (p. 11), evaluated on $df,dg$: $G(df,dg)=\sum_k\big(\partial_{q_k}f\,\partial_{q_k}g+\partial_{p_k}f\,\partial_{p_k}g\big)$.
--   9. **The momentum map** $\mu(\psi)=\rho_\psi=|\psi\rangle\langle\psi|$, the matrix with entries $\psi_i\overline{\psi_j}$.
--   10. **The linear function** $\widehat A$ on $\mathfrak u^*(\mathcal H)$, identified with Hermitian matrices $\xi$ via the pairing (4): $\widehat A(\xi)=\operatorname{Re}\tfrac12\operatorname{Tr}(\xi A)$.
--   11. **The Poisson tensor (11)** applied to $\alpha(A),\alpha(B)$: $\Lambda(d\widehat A,d\widehat B)(\xi)=\operatorname{Re}\tfrac i2\operatorname{Tr}\,\xi\big(\alpha(A)\alpha(B)-\alpha(B)\alpha(A)\big)$.
--   12. **The Jordan tensor (12)**, right-most form: $\mathcal R(\xi)(d\widehat A,d\widehat B)=\operatorname{Re}\tfrac12\operatorname{Tr}\,\xi(AB+BA)$.
--
--   These are the objects that Proposition 5 relates: the momentum map pulls the linear functions, the Lie–Poisson tensor and the Jordan tensor on $\mathfrak u^*(\mathcal H)$ back to the quadratic functions, the canonical Poisson bracket and the Euclidean structure on $\mathbb C^n$.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℂ` and vectors `Fin n → ℂ`. The derivatives are Mathlib's `fderiv ℝ` (Fréchet derivative over the reals) applied to the directions `Pi.single k 1` and `Pi.single k I`; all functions they are applied to in this mission are real quadratic forms, hence differentiable. $\mathfrak u^*(\mathcal H)$ is identified with Hermitian matrices as on p. 10, and the real-valued tensors take the real part of trace expressions that are real on Hermitian arguments. Λ is (11) evaluated at $\alpha(A),\alpha(B)$ and $\widehat A$ uses the pairing (4) (not (5)); these are the conventions under which Proposition 5 holds as printed.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, pp. 4–12, eqs. (2)–(6), (11)–(12), §3.1.1–3.1.2, Lemma 5, Proposition 5

import Mathlib

namespace GeomQM.MomentumMap
open Matrix

/-- (2), p. 4: α : O → u(H), α(A) = iA. -/
noncomputable def alpha {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • A

/-- (3), p. 4: the Lie product on observables, [A, B]₋ = α⁻¹(α(A)α(B) − α(B)α(A)) = i(AB − BA). -/
noncomputable def lieO {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • (A * B - B * A)

/-- (6), p. 4: the Jordan product A ◦ B = ½(AB + BA). -/
noncomputable def jordan {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (A * B + B * A)

/-- (4), p. 4: the scalar product ⟨A, B⟩ = ½ Tr(AB), as a complex number. -/
noncomputable def scal {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (1 / 2 : ℂ) * (A * B).trace

/-- Lemma 5, p. 12: the complex quadratic function f_A(ψ) = ½⟨ψ|Aψ⟩. -/
noncomputable def quadFnC {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (star ψ ⬝ᵥ (A *ᵥ ψ))

/-- f_A as a real function on ℂⁿ ≅ ℝ²ⁿ: the real part of `quadFnC A ψ`. -/
noncomputable def quadFn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ψ : Fin n → ℂ) : ℝ :=
  (quadFnC A ψ).re

/-- ∂f/∂q_k for the coordinates z_k = q_k + i p_k (p. 11): derivative along e_k. -/
noncomputable def dq {n : ℕ} (k : Fin n) (f : (Fin n → ℂ) → ℝ) (ψ : Fin n → ℂ) : ℝ :=
  fderiv ℝ f ψ (Pi.single k 1)

/-- ∂f/∂p_k for the coordinates z_k = q_k + i p_k (p. 11): derivative along i·e_k. -/
noncomputable def dp {n : ℕ} (k : Fin n) (f : (Fin n → ℂ) → ℝ) (ψ : Fin n → ℂ) : ℝ :=
  fderiv ℝ f ψ (Pi.single k Complex.I)

/-- The canonical Poisson bracket, p. 12:
{f, g} = Σ_k (∂f/∂q_k ∂g/∂p_k − ∂f/∂p_k ∂g/∂q_k). -/
noncomputable def poisson {n : ℕ} (f g : (Fin n → ℂ) → ℝ) (ψ : Fin n → ℂ) : ℝ :=
  ∑ k, (dq k f ψ * dp k g ψ - dp k f ψ * dq k g ψ)

/-- The contravariant Euclidean structure G = Σ_k (∂/∂q_k ⊗ ∂/∂q_k + ∂/∂p_k ⊗ ∂/∂p_k) of p. 11,
evaluated on df, dg. -/
noncomputable def metricG {n : ℕ} (f g : (Fin n → ℂ) → ℝ) (ψ : Fin n → ℂ) : ℝ :=
  ∑ k, (dq k f ψ * dq k g ψ + dp k f ψ * dp k g ψ)

/-- Proposition 5, p. 12: the momentum map µ(ψ) = ρ_ψ = |ψ⟩⟨ψ|. -/
noncomputable def momentumMap {n : ℕ} (ψ : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  vecMulVec ψ (star ψ)

/-- The linear function Â on u*(H) ≅ Hermitian matrices, Â(ξ) = ⟨ξ, A⟩ = ½ Tr(ξA) (pairing (4)). -/
noncomputable def linFn {n : ℕ} (A ξ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((1 / 2 : ℂ) * (ξ * A).trace).re

/-- (11), p. 6, applied to α(A), α(B):
Λ(dÂ, dB̂)(ξ) = (i/2) Tr ξ(α(A)α(B) − α(B)α(A)). -/
noncomputable def kks {n : ℕ} (ξ A B : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((Complex.I / 2) * (ξ * (alpha A * alpha B - alpha B * alpha A)).trace).re

/-- (12), p. 6, right-most form: R(ξ)(dÂ, dB̂) = ½ Tr ξ(AB + BA). -/
noncomputable def jordanTensor {n : ℕ} (ξ A B : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((1 / 2 : ℂ) * (ξ * (A * B + B * A)).trace).re

end GeomQM.MomentumMap


