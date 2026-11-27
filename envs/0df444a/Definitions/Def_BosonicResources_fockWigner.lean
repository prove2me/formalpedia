-- Prove2me | Definitions.Def_BosonicResources_fockWigner
-- name    : BosonicResources_fockWigner
-- status  : Definition
-- author  : @Senrui Chen
-- created : 2026-11-27T05:21:34.033952+00:00
-- url     : https://prove2.me/theorems/5f03c0ce-5439-4d0f-a714-38ad752afb4d
-- title:
--   Wigner function of the Fock matrix unit $\lvert u\rangle\langle v\rvert$
-- statement:
--   Consider an $n$-mode bosonic system with Fock basis $\lvert u\rangle$, $u=(u_1,\dots,u_n)\in\mathbb N^n$, and phase-space points $r=(q_1,\dots,q_n,p_1,\dots,p_n)\in\mathbb R^{2n}$ (positions first, then momenta). For $u,v\in\mathbb N^n$ the Wigner function of the Fock matrix unit $\lvert u\rangle\langle v\rvert$ is defined by
--
--   $$
--   W_{\lvert u\rangle\langle v\rvert}(r)=\pi^{-n}\,(-1)^{\lvert u\rvert}\prod_{j=1}^{n}\big\langle v_j\big\rvert\, D\big(\sqrt2\,(q_j+i\,p_j)\big)\,\big\lvert u_j\big\rangle ,
--   $$
--
--   where $\lvert u\rvert=\sum_j u_j$ is the total photon number and $\langle m\rvert D(z)\lvert k\rangle$ is the Fock matrix element of the one-mode displacement operator $D(z)=\exp(z\,a^\dagger-\bar z\,a)$.
--
--   This is the Wigner function of Sec. 2 of the paper, $W_{\hat O}(r)=(2\pi)^{-2n}\int d^{2n}\xi\,\exp(i\xi^{T}\Omega r)\operatorname{Tr}[\hat O\hat D(\xi)]$, evaluated on the operators $\hat O=\lvert u\rangle\langle v\rvert$. Since every operator is determined by its Fock matrix elements, these functions are what is needed to say that a POVM element has a prescribed Wigner function (the definition of classical measurements) and that the Wigner function of the Gaussian state $\rho(\mu,\Sigma)$ is the density of $\mathcal N(\mu,\Sigma)$.
--
--   **Formalization Note** For a trace-class operator $T$ the paper's Fourier formula equals the displaced-parity formula $W_T(r)=\pi^{-n}\operatorname{Tr}[T\,D(\alpha)\,\Pi\,D(\alpha)^\dagger]$ with $\alpha_j=(q_j+i\,p_j)/\sqrt2$ and $\Pi=(-1)^{\hat N}$ (Royer 1977); since $D(\alpha)\Pi D(\alpha)^\dagger=D(2\alpha)\Pi$, for $T=\lvert u\rangle\langle v\rvert$ this is the expression above. Conventions: $\hat q=(\hat a+\hat a^\dagger)/\sqrt2$, $\hat p=(\hat a-\hat a^\dagger)/(i\sqrt2)$, so the vacuum has $W_{\lvert 0\rangle\langle 0\rvert}(r)=\pi^{-n}e^{-\|r\|^2}$, the density of $\mathcal N(0,\tfrac12 I)$. The paper's formula as printed returns $W_\rho(-r)$ (its sign convention for $\hat D(\xi)$); the sign is fixed here so that a Gaussian state $\rho(\mu,\Sigma)$ has Wigner function $\mathcal N(\mu,\Sigma)$, as the paper states. The matrix elements $\langle m\rvert D(z)\lvert k\rangle$ are the published `Dependency50.P39.displacementMatrix`; the Lean name is `fockWigner u v r`.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (definition of the Wigner function of an operator, its normalization and the trace formula)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicResources

/-- **Wigner function of the Fock matrix unit `|u⟩⟨v|`.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "For any operator Ô, the Wigner function of it is defined by
W_Ô(r) := (2π)^{-2n} ∫ d^{2n}ξ exp(iξᵀΩr) Tr[Ô D̂(ξ)]. For a density operator ρ, its Wigner function satisfies the
normalization condition ∫ d^{2n}r W_ρ(r) = 1. Any observable expectation value can be computed using Wigner functions
according to Tr(ρÔ) = (2π)^n ∫ d^{2n}r W_ρ(r) W_Ô(r)."

For occupation vectors `u, v ∈ ℕⁿ` and a phase-space point `r = (q₁,…,qₙ,p₁,…,pₙ) ∈ ℝ²ⁿ` (grouped order, index
`Sum.inl j` is `q_j`, `Sum.inr j` is `p_j`),

`fockWigner u v r = π^{-n} · (−1)^{|u|} · ∏ⱼ ⟨vⱼ| D(√2 (qⱼ + i pⱼ)) |uⱼ⟩`,

where `|u| = ∑ⱼ uⱼ` and `⟨m|D(z)|k⟩` is the Fock matrix element of the one-mode displacement operator
`D(z) = exp(z a† − z̄ a)` (`Dependency50.P39.displacementMatrix`).

**Formalization Note.** For a trace-class operator `T` the paper's Fourier formula equals the displaced-parity
formula `W_T(r) = π^{-n} Tr[T D(α) Π D(α)†]`, `α_j = (q_j + i p_j)/√2`, `Π = (−1)^{N̂}` (Royer 1977); since
`D(α) Π D(α)† = D(2α) Π`, for `T = |u⟩⟨v|` this is the expression above. Conventions: `q̂ = (â + â†)/√2`,
`p̂ = (â − â†)/(i√2)`, so the vacuum has `fockWigner 0 0 r = π^{-n} exp(−‖r‖²)`, the density of `N(0, ½I)`. The
paper's formula as printed returns `W_ρ(−r)` (its sign convention for `D̂(ξ)`); the sign is fixed here so that a
Gaussian state `ρ(µ, Σ)` has Wigner function `N(µ, Σ)`, as the paper states. -/
noncomputable def fockWigner {n : ℕ} (u v : Occupation (Fin n)) (r : EuclideanSpace ℝ (Fin n ⊕ Fin n)) : ℂ :=
  ((1 / Real.pi ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ (∑ j, u j) *
    ∏ j, displacementMatrix
      ((Real.sqrt 2 : ℂ) * ((r (Sum.inl j) : ℂ) + Complex.I * (r (Sum.inr j) : ℂ))) (v j) (u j)

end BosonicResources


