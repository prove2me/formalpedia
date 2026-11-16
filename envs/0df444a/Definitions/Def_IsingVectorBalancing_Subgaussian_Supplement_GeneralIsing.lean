-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_GeneralIsing
-- name    : IsingVectorBalancing_Subgaussian_Supplement_GeneralIsing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:16:27.792746+00:00
-- url     : https://prove2.me/theorems/a32ef3db-1b88-439a-98d1-5f3f6d6f4d96
-- title:
--   General Ising Gibbs law and entrywise-tanh spectrum
-- statement:
--   For a real matrix $J$ and real external field $h$, on the published sign cube define
--
--   $$\mu_{J,h}(\sigma)=\frac{\exp(\frac12\sum_{i,j}\sigma_i J_{ij}\sigma_j+\sum_i h_i\sigma_i)}{\sum_\tau\exp(\frac12\sum_{i,j}\tau_i J_{ij}\tau_j+\sum_i h_i\tau_i)}.$$
--
--   Also define $T_{ij}=\tanh J_{ij}$ entrywise. The largest real eigenvalue is the supremum of the real numbers having a nonzero real eigenvector. In every use the matrix is real symmetric in positive dimension, so its eigenvalue set is finite and nonempty and the supremum is its algebraically largest eigenvalue. No absolute value, spectral radius or matrix functional calculus is involved. This is the model and spectral vocabulary of Theorem 3.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 2 (PDF 3), (2), Theorem 3

import Definitions.Def_IsingVectorBalancing_Subgaussian_Law

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Equation (2), including its positive quadratic sign and factor 1/2. -/
noncomputable def isingWeight {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (σ : Configuration n) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * (∑ i, ∑ j, spin (σ i) * J i j * spin (σ j)) +
    ∑ i, h i * spin (σ i))

noncomputable def isingLaw {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (σ : Configuration n) : ℝ :=
  isingWeight J h σ / ∑ τ : Configuration n, isingWeight J h τ

noncomputable def tanhMatrix {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => Real.tanh (J i j)

/-- Algebraically largest real eigenvalue. For a symmetric matrix with n>0,
the set is nonempty and finite; it counts no absolute values or matrix norms. -/
noncomputable def largestEigenvalue {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {x : ℝ | ∃ u : Fin n → ℝ, u ≠ 0 ∧
    ∀ i, (∑ j, M i j * u j) = x * u i}

end IsingVectorBalancing.Subgaussian.Supplement


