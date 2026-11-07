-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_IsLSEstimator
-- name    : OptimalSpectrum_Entangled_IsLSEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:18.098003+00:00
-- url     : https://prove2.me/theorems/4461d010-3082-474e-8256-9fbc7c6d0972
-- title:
--   Least-squares Chebyshev moment-matching estimator $\widehat z$
-- statement:
--   Given moment estimates and polynomials $q_1,\dots,q_K$ (either $q_k=\phi_k$ or $q_k=\psi_k$), $\widehat z$ is a **least-squares estimator** when for every outcome
--
--   $$\widehat z\in\arg\min_{z\in Z_d}\ \sum_{k=1}^K\frac1{k^2}\Big(\widehat F_{q_k}-\sum_{i=1}^d q_k(z_i)\Big)^2 .$$
--
--   It is the spectrum estimator of Propositions 6.1 and 6.2 and step 3 of Algorithm 8.1.
--
--   **Formalization Note** Any selection from the arg min qualifies; measurability is a separate hypothesis where an expectation is taken.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Propositions 6.1–6.2, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_Zd
import Definitions.Def_OptimalSpectrum_Entangled_estF

namespace OptimalSpectrum.Entangled

/-- **Least-squares Chebyshev moment-matching estimator.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Propositions 6.1 and 6.2, printed p. 14 (PDF p. 16): "Define the spectrum estimator as
ẑ ∈ arg min_(z∈Z_d) ∑_(k=1)^K (1/k²)(F̂_(q_k) − ∑_(i=1)^d q_k(z_i))²", with `q_k = ϕ_k` (Prop. 6.1)
or `q_k = ψ_k` (Prop. 6.2).

`IsLSEstimator d L K M̂ q ẑ` says that for every outcome `ω`, `ẑ(ω) ∈ Z_d` and `ẑ(ω)` minimizes the
weighted least-squares objective over `Z_d`.

**Formalization Note.** `ẑ` is any selection from the arg min, outcome by outcome; measurability of
the selection is a separate hypothesis where an expectation of `ẑ` is taken. -/
def IsLSEstimator {Ω : Type*} (d : ℕ) (L : ℝ) (K : ℕ) (Mhat : ℕ → Ω → ℝ)
    (q : ℕ → Polynomial ℝ) (zhat : Ω → Fin d → ℝ) : Prop :=
  ∀ ω, zhat ω ∈ Zd d L ∧ ∀ z ∈ Zd d L,
    ∑ k ∈ Finset.Icc 1 K, (1 / (k : ℝ) ^ 2) *
        (estF d K Mhat (q k) ω - ∑ i, (q k).eval (zhat ω i)) ^ 2 ≤
      ∑ k ∈ Finset.Icc 1 K, (1 / (k : ℝ) ^ 2) * (estF d K Mhat (q k) ω - ∑ i, (q k).eval (z i)) ^ 2

end OptimalSpectrum.Entangled


