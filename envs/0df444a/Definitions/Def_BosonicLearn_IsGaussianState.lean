-- Prove2me | Definitions.Def_BosonicLearn_IsGaussianState
-- name    : BosonicLearn_IsGaussianState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:41.300311+00:00
-- url     : https://prove2.me/theorems/5b8f059e-b763-438d-ad1b-2720059eab12
-- title:
--   The $n$-mode Gaussian state $\rho(\mu,\Sigma)$ (vacuum covariance $\tfrac12 I$)
-- statement:
--   Let $\mathcal H^{(n)}=\ell^2(\mathbb N^n)$ be the Fock space of $n$ bosonic modes, with ladder operators $\hat a_j$ and quadratures in **grouped** order $\hat{\boldsymbol r}=(\hat q_1,\dots,\hat q_n,\hat p_1,\dots,\hat p_n)$, where
--
--   $$\hat q_j=\frac{\hat a_j+\hat a_j^\dagger}{\sqrt2},\qquad \hat p_j=\frac{\hat a_j-\hat a_j^\dagger}{i\sqrt2}.$$
--
--   A density operator $\rho$ is the **Gaussian state** $\rho(\mu,\Sigma)$ with mean $\mu\in\mathbb R^{2n}$ and covariance $\Sigma\in\mathbb R^{2n\times 2n}$ if its characteristic function is Gaussian,
--
--   $$\operatorname{Tr}\big(\rho\, e^{i\xi^{T}\hat{\boldsymbol r}}\big)=\exp\!\Big(i\,\xi^T\mu-\tfrac12\,\xi^T\Sigma\,\xi\Big)\qquad(\xi\in\mathbb R^{2n}),$$
--
--   with $\mu_j=\operatorname{Tr}(\rho\hat r_j)$ and $\Sigma_{kl}=\tfrac12\operatorname{Tr}(\rho\{\hat r_k-\mu_k,\hat r_l-\mu_l\})$. In this convention the vacuum has $\Sigma=\tfrac12 I$.
--
--   All statements of the mission use this convention: the promise $\Sigma\succeq(\tfrac12+\nu)I$ measures the distance from the vacuum.
--
--   **Formalization Note** The predicate is the published `Support50.P14.GaussianAt` (Gaussian characteristic function together with finite energy, symmetry and the moment identities, which every Gaussian state satisfies), applied after two convention changes: P14 orders quadratures interleaved, $(q_1,p_1,q_2,p_2,\dots)$, and uses the covariance $\gamma=2\Sigma$ (vacuum $\gamma=I$). Index `Sum.inl j` is $\hat q_j$ and `Sum.inr j` is $\hat p_j$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt)

namespace BosonicLearn

/-- **The `n`-mode Gaussian state `ρ(µ, Σ)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5: "A *Gaussian state* is a state whose Wigner function is a
Gaussian distribution, i.e. W_ρ = N(µ, Σ). Such a state is completely determined by its first and second
moments, µ_j = Tr(ρ r̂_j), Σ_kl := 1/2 Tr(ρ{r̂_k − µ_k, r̂_l − µ_l}); thus we denote a Gaussian state by ρ(µ, Σ)."

`IsGaussianState ρ μ S` says the density operator `ρ` on the Fock space `ℓ²(ℕⁿ)` is the Gaussian state with
mean `µ` and covariance matrix `S` in the paper's conventions: quadratures in **grouped** order
`r̂ = (q̂₁,…,q̂ₙ,p̂₁,…,p̂ₙ)` (index `Sum.inl j` is `q̂_j`, `Sum.inr j` is `p̂_j`), `q̂ = (â+â†)/√2`,
`p̂ = (â−â†)/(i√2)`, and `Σ_kl = ½ Tr(ρ{r̂_k − µ_k, r̂_l − µ_l})`, so that the **vacuum has `Σ = ½ I`**.

**Formalization Note.** It is the published predicate `Support50.P14.GaussianAt` (characteristic function
`Tr(ρ e^{iξ·r̂}) = exp(iξ·d − ¼ ξᵀγξ)`, plus finite energy, symmetry of `γ` and the moment identities, all of
which hold for every Gaussian state), after two convention changes: P14 indexes quadratures *interleaved*,
`(j,0) = q̂_j`, `(j,1) = p̂_j`, and uses the full anticommutator covariance `γ = 2Σ` (vacuum `γ = I`). So
`d (j,k) = µ (q_j or p_j)` and `γ = 2·Σ` reindexed. Check: the paper's characteristic function is
`exp(iξ·µ − ½ ξᵀΣξ)`, and `¼ ξᵀ(2Σ)ξ = ½ ξᵀΣξ`. -/
def IsGaussianState {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : Prop :=
  GaussianAt ρ.coefficients
    (fun a => μ (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1))
    (fun a b => 2 * S (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)
      (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1))

end BosonicLearn


