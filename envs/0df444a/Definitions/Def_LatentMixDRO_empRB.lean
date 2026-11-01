-- Prove2me | Definitions.Def_LatentMixDRO_empRB
-- name    : LatentMixDRO_empRB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:45.04057+00:00
-- url     : https://prove2.me/theorems/4e8dbf73-ccb6-41b0-ab50-11788687e4aa
-- title:
--   Empirical loss $\widehat R_{p,\epsilon,L}(\theta,\eta,B)$ (15) (corrected: coefficient $1/n$)
-- statement:
--   For a sample, $B\in\mathbb R_+^{n\times n}$ and $\epsilon>0$,
--
--   $$
--   \widehat R_{p,\epsilon,L}(\theta,\eta,B)=\Big(\frac1n\sum_{i=1}^n\Big(\ell(\theta;(X_i,Y_i))-\frac1n\sum_{j=1}^n(B_{ij}-B_{ji})-\eta\Big)_+^{\,p}\Big)^{1/p}+\frac{L^{p-1}}{\epsilon n^2}\sum_{i,j=1}^n\|X_i-X_j\|^{p-1}B_{ij}.
--   $$
--
--   The dual variables $B_{ij}$ act as a transport plan: losses are moved between sample points at a distance-dependent cost.
--
--   **Formalization Note** The leading coefficient is $1/n$. The page prints $(p-1)/n$, under which Lemma 4.1 is false for $p<2$: at $n=1$, $\ell=1$, $\eta=0$, $p=3/2$, the plug-in (14) is $1$ while the printed (15) is $(1/2)^{2/3}$ for every $B$. The derivation on p.37 writes $1/(q\lambda^{p-1}n)$ where $1/(p\lambda^{p-1}n)$ belongs. The two coefficients agree at $p=2$.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (15), p.10

import Mathlib

namespace LatentMixDRO

/-- The empirical loss of (15), with the corrected leading coefficient `1/n`:
`R̂_{p,ε,L}(θ, η, B) = ((1/n) ∑ᵢ (ℓ(θ; (Xᵢ, Yᵢ)) - (1/n) ∑ⱼ (B_ij - B_ji) - η)₊^p)^{1/p}
  + (L^{p-1}/(ε n²)) ∑_{i,j} ‖Xᵢ - Xⱼ‖^{p-1} B_ij`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (15), p.10.

**Formalization Note.** Correction: the page prints the coefficient `(p - 1)/n`. With it Lemma 4.1 is
false for `p < 2` (`n = 1`, `ℓ = 1`, `η = 0`, `p = 3/2`: (14) is `1`, the printed (15) is `(1/2)^{2/3}`
for every `B`); the derivation on p.37 writes `1/(q λ^{p-1} n)` where `1/(p λ^{p-1} n)` belongs. The
two coefficients agree at `p = 2`. -/
noncomputable def empRB {d n : ℕ} {Θ : Type*} (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ)
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (p ε L : ℝ) (θ : Θ) (η : ℝ)
    (B : Fin n → Fin n → ℝ) : ℝ :=
  ((1 / (n : ℝ)) * ∑ i, (max (ℓ θ (ω i) - (1 / (n : ℝ)) * (∑ j, (B i j - B j i)) - η) 0) ^ p)
      ^ (1 / p)
    + L ^ (p - 1) / (ε * (n : ℝ) ^ 2) * ∑ i, ∑ j, ‖(ω i).1 - (ω j).1‖ ^ (p - 1) * B i j

end LatentMixDRO


