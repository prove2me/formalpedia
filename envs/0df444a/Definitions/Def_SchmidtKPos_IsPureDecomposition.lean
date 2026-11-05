-- Prove2me | Definitions.Def_SchmidtKPos_IsPureDecomposition
-- name    : SchmidtKPos_IsPureDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:34.102785+00:00
-- url     : https://prove2.me/theorems/4f0e7a62-4134-4e62-8303-92348dcb9bc6
-- title:
--   Pure-state decomposition $\rho=\sum_i p_i|\psi_i\rangle\langle\psi_i|$ (Definition 1)
-- statement:
--   Let $\rho$ be an operator on $\mathcal H_n\otimes\mathcal H_n$, where $\mathcal H_n=\mathbb C^n$. A family of weights $p_1,\dots,p_r\ge 0$ and unit vectors $|\psi_1\rangle,\dots,|\psi_r\rangle\in\mathcal H_n\otimes\mathcal H_n$ is a **decomposition** of $\rho$ when
--
--   $$
--   \rho=\sum_{i=1}^r p_i\,|\psi_i\rangle\langle\psi_i| .
--   $$
--
--   This is the notion of decomposition quantified over in the definition of the Schmidt number.
--
--   **Formalization Note** The family is finite, indexed by `Fin r`, and zero weights are allowed. The condition $\sum_i p_i=1$ is not assumed: it follows from $\operatorname{Tr}\rho=1$ when $\rho$ is a density matrix.
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Definition 1, p. 1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Definition 1, p.1: a decomposition `{p_i ≥ 0, |ψ_i⟩}` of `ρ`, that is
`ρ = Σ_i p_i |ψ_i⟩⟨ψ_i|`.

**Formalization Note.** The decomposition is finite (`Fin r`) and the `ψ_i` are unit vectors, the
paper's convention for pure states; a countable decomposition in finite dimension reduces to a
finite one and a non-unit vector is absorbed into its weight. Zero weights are allowed, as the
paper's `p_i ≥ 0` allows them. `Σ_i p_i = 1` is not assumed: it follows from `Tr ρ = 1`.
`QAlgorithms.pureDensity ψ` is `|ψ⟩⟨ψ|`, with no normalizing factor. -/
def IsPureDecomposition {n : ℕ} (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    {r : ℕ} (p : Fin r → ℝ) (ψ : Fin r → EuclideanSpace ℂ (Fin n × Fin n)) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∀ i, ‖ψ i‖ = 1) ∧ ρ = ∑ i, (p i : ℂ) • QAlgorithms.pureDensity (ψ i)

end SchmidtKPos


