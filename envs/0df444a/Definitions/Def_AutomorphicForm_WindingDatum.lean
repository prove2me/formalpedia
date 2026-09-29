-- Prove2me | Definitions.Def_AutomorphicForm_WindingDatum
-- name    : AutomorphicForm_WindingDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/823fd7d3-429d-590c-bf1b-fe0c0a614e61
-- title:
--   Winding data: lattice fibre sums with decaying windows
-- statement:
--   This module introduces the structure [`AutomorphicForm.WindingDatum r d c`](../def/AutomorphicForm_WindingDatum.html#L11) and the coefficient array attached to it. A term of the structure consists of: an additive subgroup $\Lambda \le (\mathrm{Fin}\,r \to \mathbb R) \times (\mathrm{Fin}\,d \to \mathbb Z)$ carrying the discrete topology (the field `hΛ` asserts `DiscreteTopology Λ`); an $\mathbb R$-linear form $s$ on $\mathbb R^r$; a vector $\omega \in \mathbb R^d$ with $\omega \neq 0$ (as a function); a product-formula field `hpf` asserting $s(x_1) = \sum_i \omega_i (x_2)_i$ for every $x = (x_1,x_2) \in \Lambda$; an additive homomorphism $\chi : \Lambda \to (\mathrm{Fin}\,c \to \mathbb{R}/\mathbb{Z})$, the target being Mathlib's `AddCircle (1 : ℝ)`; and a family indexed by $i \in \mathbb N$ of subgroups `sub i` of the ambient group, each contained in $\Lambda$, of functions $\Psi_i : \mathbb R^r \to \mathbb C$ that are continuous and integrable, of constants $C_i \in \mathbb R$, of exponents $m_i \in \mathbb Z^c$, phases $\theta_{0,i} \in (\mathbb R/\mathbb Z)^c$, shifts $x_{0,i} \in \mathbb R^r$ and $n_{0,i} \in \mathbb Z^d$, and scalars $\lambda_i \in \mathbb C$. Three analytic laws are fields: the pointwise bounds $\|\Psi_i(x)\| \le C_i \prod_k (1+|x_k|)^{-2}$, the same bound with $\xi$ in place of $x$ for the explicitly written Fourier integral $\int_{\mathbb R^r} e^{-2\pi i \sum_k \xi_k x_k} \Psi_i(x)\,dx$, and the summability of $i \mapsto \|\lambda_i\| C_i$.
--
--   From such a datum, `fibreTerm i n γ`, for $\gamma$ in `sub i`, is defined to be $\Psi_i(x_{0,i} + \gamma_1) \prod_j e_{m_{i,j}}(\theta_{0,i,j} + \chi(\gamma)_j)$ when $\gamma_2 + n_{0,i} = n$ and $0$ otherwise, where $e_m$ is Mathlib's character `fourier` on the circle; `fibreCoeff i n` is the unconditional sum of these terms over all $\gamma \in$ `sub i`, and `coeff n` is the unconditional sum over $i$ of $\lambda_i \cdot$ `fibreCoeff i n`. Two elementary lemmas record that `fibreTerm` vanishes off the fibre $\gamma_2 + n_{0,i} = n$, and that `coeff` vanishes identically when all $\lambda_i$ are zero.
--
--   **Relation to Mathlib.** Mathlib has no notion of winding datum; the structure is the project's own, built on Mathlib's `AddSubgroup`, `DiscreteTopology`, `Integrable`, `AddCircle` and the characters `fourier`.
--
--   **Where it is used.** The structure packages the input data of a winding statement: a coefficient array indexed by $n \in \mathbb Z^d$, assembled from twisted lattice-fibre sums of windows of product-decay class, to be interpolated by a continuous functional on $C(\mathbb T^d)$. It is a shared input format for the later trace-formula comparisons, whose residual class-sum arrays are finite sums of congruence-coset contributions together with absolutely convergent series of such fibre sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WindingDatum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace AutomorphicForm

structure WindingDatum (r d c : ℕ) where

  Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))

  hΛ : DiscreteTopology Λ

  s : (Fin r → ℝ) →ₗ[ℝ] ℝ

  ω : Fin d → ℝ

  hω : ω ≠ 0

  hpf : ∀ x ∈ Λ, s x.1 = ∑ i, ω i * (x.2 i : ℝ)

  χ : Λ →+ (Fin c → AddCircle (1 : ℝ))

  sub : ℕ → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))

  hsub : ∀ i : ℕ, sub i ≤ Λ

  Ψ : ℕ → (Fin r → ℝ) → ℂ

  hΨc : ∀ i : ℕ, Continuous (Ψ i)

  hΨi : ∀ i : ℕ, Integrable (Ψ i)

  C : ℕ → ℝ

  hΨd : ∀ (i : ℕ) (x : Fin r → ℝ), ‖Ψ i x‖ ≤ C i * ∏ k, (1 + |x k|)⁻¹ ^ 2

  hΨhatd : ∀ (i : ℕ) (ξ : Fin r → ℝ),
    ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Ψ i x‖ ≤
      C i * ∏ k, (1 + |ξ k|)⁻¹ ^ 2

  m : ℕ → Fin c → ℤ

  θ₀ : ℕ → Fin c → AddCircle (1 : ℝ)

  x₀ : ℕ → Fin r → ℝ

  n₀ : ℕ → Fin d → ℤ

  lam : ℕ → ℂ

  hsum : Summable fun i : ℕ => ‖lam i‖ * C i

namespace WindingDatum

variable {r d c : ℕ} (𝒟 : WindingDatum r d c)

def fibreTerm (i : ℕ) (n : Fin d → ℤ) (γ : 𝒟.sub i) : ℂ :=
  if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i = n then
    𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
      ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j)
  else 0

def fibreCoeff (i : ℕ) (n : Fin d → ℤ) : ℂ :=
  ∑' γ : 𝒟.sub i, 𝒟.fibreTerm i n γ

def coeff (n : Fin d → ℤ) : ℂ :=
  ∑' i : ℕ, 𝒟.lam i * 𝒟.fibreCoeff i n

theorem fibreTerm_of_ne (i : ℕ) (n : Fin d → ℤ) (γ : 𝒟.sub i)
    (h : (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i ≠ n) : 𝒟.fibreTerm i n γ = 0 :=
  if_neg h

theorem coeff_eq_zero_of_lam_eq_zero (h : ∀ i : ℕ, 𝒟.lam i = 0) (n : Fin d → ℤ) : 𝒟.coeff n = 0 := by
  simp [coeff, h]

end WindingDatum

end AutomorphicForm

end


