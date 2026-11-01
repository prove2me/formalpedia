-- Prove2me | Definitions.Def_LatentMixDRO_empR
-- name    : LatentMixDRO_empR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:34.63244+00:00
-- url     : https://prove2.me/theorems/1819d077-e0a6-4b0a-96aa-32672d911d89
-- title:
--   Empirical plug-in $\widehat R_{p,\epsilon,L}(\theta,\eta)$ (14)
-- statement:
--   With $q=p/(p-1)$, $\epsilon>0$ and $\widehat P_n$ the empirical law of the sample $(X_1,Y_1),\dots,(X_n,Y_n)$,
--
--   $$
--   \widehat R_{p,\epsilon,L}(\theta,\eta)=\sup_{h\in\widehat{\mathcal H}_{L,p}}\Big\{\mathbb E_{\widehat P_n}\Big[\frac{h(X)}{\epsilon}\big(\ell(\theta;(X,Y))-\eta\big)\Big]\ \Big|\ h\ge0,\ \big(\mathbb E_{\widehat P_n}[h^q(X)]\big)^{1/q}\le\epsilon\Big\}.
--   $$
--
--   This is the sample version of (12), and a finite-dimensional convex program.
--
--   **Formalization Note** Empirical means are finite sums. For $n\ge1$ the set of values contains $0$ and is bounded above, so the real supremum is the true one.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (14), p.10

import Mathlib
import Definitions.Def_LatentMixDRO_empHolderClass

namespace LatentMixDRO

/-- The empirical plug-in
`R̂_{p,ε,L}(θ, η) = sup_{h ∈ Ĥ_{L,p}} {E_{P̂_n}[(h(X)/ε)(ℓ(θ; (X, Y)) - η)] | h ≥ 0, (E_{P̂_n}[h^q(X)])^{1/q} ≤ ε}`,
with `q = p/(p - 1)`, for the sample `ω = ((X₁, Y₁), …, (X_n, Y_n))`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (14), p.10.

**Formalization Note.** Empirical means are finite sums. For `n ≥ 1` and `ε > 0` the set is nonempty
(`h = 0`) and bounded above (`h i ≤ ε n^{1/q}`), so `sSup` is the true supremum. -/
noncomputable def empR {d n : ℕ} {Θ : Type*} (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ)
    (ℓ : Θ → EuclideanSpace ℝ (Fin d) × ℝ → ℝ) (p ε L : ℝ) (θ : Θ) (η : ℝ) : ℝ :=
  sSup {v | ∃ h ∈ empHolderClass ω p L, (∀ i, 0 ≤ h i) ∧
    ((1 / (n : ℝ)) * ∑ i, h i ^ (p / (p - 1))) ^ (1 / (p / (p - 1))) ≤ ε ∧
    v = (1 / (n : ℝ)) * ∑ i, h i / ε * (ℓ θ (ω i) - η)}

end LatentMixDRO


