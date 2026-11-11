-- Prove2me | Definitions.Def_HermiteLaptop_MaxAgree_Mixture
-- name    : HermiteLaptop_MaxAgree_Mixture
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:16:29.418574+00:00
-- url     : https://prove2.me/theorems/ed05f28e-39a6-4aa6-b1a0-dea7104bafe8
-- title:
--   Mixtures of k-spokes roundings: probabilities (λ_k)_{k∈K}, collision probability P = Σ λ_k P_k and expected value (Corollary 2.2, Lemma 4.1)
-- statement:
--   Let $\mathcal K$ be a set of positive integers (possibly infinite) and $\lambda=(\lambda_k)_{k\in\mathcal K}$ with $\lambda_k\ge0$ and $\sum_{k\in\mathcal K}\lambda_k=1$. The **mixture** of k-spokes roundings draws $k$ with probability $\lambda_k$ and applies k-spokes. Its collision probability and its expected value on an instance are
--   $$P(\rho)=\sum_{k\in\mathcal K}\lambda_k P_k(\rho),\qquad \mathbb E[\mathrm{val}]=\sum_{k\in\mathcal K}\lambda_k\,\mathbb E[\mathrm{val}(k\text{-spokes}(v))].$$
--
--   **Formalization Note.** `Mixture` stores `K : Set ℕ` (positive elements), `lam : ℕ → ℝ` nonnegative, zero off `K`, with `HasSum lam 1`. `Mixture.collision ρ = ∑' k, lam k * collisionProb k ρ` and `Mixture.value I v = ∑' k, lam k * I.spokesValue k v` (both series converge: the terms are bounded multiples of `lam k`).
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 15 (PDF 18), Corollary 2.2; p. 26 (PDF 29), Lemma 4.1

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_KSpokes

/-!
# Mixtures of k-spokes roundings and their collision probability

García-Soriano, Miyauchi, *Hermite Brings a Laptop*, arXiv:2609.35453 (held version, sha256
97504f90…), Corollary 2.2 p. 15 (PDF 18); Lemma 4.1 p. 26 (PDF 29).

"Let K be a set of positive integers. Consider the mixture of the k-spokes roundings with
probabilities λ = (λk)k∈K, where λk ≥ 0 and Σ_{k∈K} λk = 1."

Conventions.
* `K : Set ℕ` is a set of positive integers, possibly infinite. The probabilities are a function
  `lam : ℕ → ℝ`, nonnegative, zero off `K`, with `HasSum lam 1` (`Σ_{k∈K} λ_k = 1`; a series of
  nonnegative terms).
* The mixture draws `k` with probability `λ_k` and applies k-spokes; by total probability its
  collision probability is `P(ρ) = Σ_k λ_k P_k(ρ)` (the series converges: `0 ≤ P_k ≤ 1`), and its
  expected value on an instance is `Σ_k λ_k E[val(k-spokes)]`.
-/

namespace HermiteLaptop.MaxAgree

/-- A mixture of k-spokes roundings: a set `K` of positive integers and probabilities
`λ = (λ_k)_{k∈K}`, `λ_k ≥ 0`, `Σ_{k∈K} λ_k = 1` (stored as `lam : ℕ → ℝ`, zero off `K`). -/
structure Mixture where
  /-- the set `K` of spoke counts -/
  K : Set ℕ
  /-- the probabilities `λ_k` (zero off `K`) -/
  lam : ℕ → ℝ
  /-- `K` is a set of positive integers -/
  K_pos : ∀ k ∈ K, 0 < k
  /-- `λ_k ≥ 0` -/
  lam_nonneg : ∀ k, 0 ≤ lam k
  /-- `λ` is supported on `K` -/
  lam_zero_off : ∀ k, k ∉ K → lam k = 0
  /-- `Σ_{k∈K} λ_k = 1` -/
  lam_sum : HasSum lam 1

/-- The collision probability of the mixture: `P(ρ) = Σ_{k∈K} λ_k P_k(ρ)`. -/
noncomputable def Mixture.collision (μ : Mixture) (ρ : ℝ) : ℝ :=
  ∑' k, μ.lam k * collisionProb k ρ

/-- The expected value of the mixture's output on the SDP vectors `v`:
`Σ_{k∈K} λ_k E[val(k-spokes(v))]`. -/
noncomputable def Mixture.value (μ : Mixture) {n : ℕ} (I : Instance n)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑' k, μ.lam k * I.spokesValue k v

end HermiteLaptop.MaxAgree


