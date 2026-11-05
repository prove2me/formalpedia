-- Prove2me | Definitions.Def_SchmidtKPos_IsMaxEntangledRank
-- name    : SchmidtKPos_IsMaxEntangledRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:31.781747+00:00
-- url     : https://prove2.me/theorems/94c0916c-713f-4d45-8ade-cb3676cab03c
-- title:
--   Maximally entangled Schmidt rank $k$ vector
-- statement:
--   A vector $|\Psi_k\rangle\in\mathbb C^n\otimes\mathbb C^m$ is a **maximally entangled Schmidt rank $k$ vector** if
--
--   $$
--   |\Psi_k\rangle=\frac{1}{\sqrt k}\sum_{i=1}^k|\gamma_i\rangle\otimes|a_i\rangle
--   $$
--
--   for orthonormal families $\{|\gamma_i\rangle\}_{i=1}^k\subset\mathbb C^n$ and $\{|a_i\rangle\}_{i=1}^k\subset\mathbb C^m$. This is the Schmidt form of Eq. (1) with all coefficients $\lambda_i=1/k$. These vectors suffice to test $k$-positivity by Lemma 3.
--
--   **Formalization Note** Such a vector exists only when $k\le n$ and $k\le m$. At $k=0$ the sum is empty and the vector is $0$.
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Lemma 3, p. 4; cf. Eqs. (10), (20)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Lemma 3, p.4: "`|Ψ_k⟩` … maximally entangled Schmidt rank `k` vectors",
that is `k^{-1/2} Σ_{i=1}^k |γ_i⟩ ⊗ |a_i⟩` with orthonormal families `γ`, `a` (Eq. (1) with all
`λ_i = 1/k`; compare Eqs. (10), (20)).

**Formalization Note.** Such a vector exists only when `k ≤ n` and `k ≤ m`. At `k = 0` the sum is
empty and the only such vector is `0`. -/
def IsMaxEntangledRank {n m : ℕ} (k : ℕ) (v : EuclideanSpace ℂ (Fin n × Fin m)) : Prop :=
  ∃ (γ : Fin k → EuclideanSpace ℂ (Fin n)) (a : Fin k → EuclideanSpace ℂ (Fin m)),
    Orthonormal ℂ γ ∧ Orthonormal ℂ a ∧
      v = (((Real.sqrt k)⁻¹ : ℝ) : ℂ) • ∑ i, QAlgorithms.tensorVec (γ i) (a i)

end SchmidtKPos


