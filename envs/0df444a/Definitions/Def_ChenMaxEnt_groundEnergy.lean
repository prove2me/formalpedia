-- Prove2me | Definitions.Def_ChenMaxEnt_groundEnergy
-- name    : ChenMaxEnt_groundEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:32.443492+00:00
-- url     : https://prove2.me/theorems/875a492f-3dba-4405-94db-d694d4a06531
-- title:
--   Ground energy of a Hamiltonian (its lowest eigenvalue)
-- statement:
--   Let $H$ be a Hamiltonian, a Hermitian operator on $\mathcal H = \mathbb C^n$. Its **ground energy** is its lowest eigenvalue,
--
--   $$
--   E_0(H) = \min \operatorname{spec}(H) .
--   $$
--
--   The paper works with Hamiltonians $H = \sum_i \theta_i F_i$ in the real span of the observables; their ground energy and ground space (the eigenspace of $E_0$) are the objects of Observation 3.
--
--   **Formalization Note** The definition is the infimum of the real numbers $E$ that are eigenvalues of $H$ acting on $\mathbb C^n$. For Hermitian $H$ on a nonzero space this set is finite and nonempty, so the infimum is the least eigenvalue. On the zero space there are no eigenvalues and the value is the junk $0$ (the ground space is the zero space either way). The definition does not take a Hermiticity proof as an argument; every Hamiltonian in this mission is a real combination of Hermitian matrices.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §5.3, Observation 3, p.22 (ground state of H0; standard notion, not separately defined in the paper)

import Mathlib

namespace ChenMaxEnt

/-- Chen et al., arXiv:1406.5046v2, §2.1 p.4, §3 and §5.3 p.22: the ground energy of a
Hamiltonian `H`, its lowest eigenvalue. (The paper uses "ground state", "ground-state space" of a
Hamiltonian `H = Σ_i θ_i F_i` throughout, e.g. Observation 3, p.22, without a separate
definition; the ground energy is the standard minimum of the spectrum.)

**Formalization Note.** `H` acts on `ℂ^n` as `Matrix.toEuclideanLin H`. The ground energy is the
infimum of the real numbers `E` that are eigenvalues of `H`. For a Hermitian `H` on a nonzero
space every eigenvalue is real and there are finitely many, so this is the least eigenvalue. For
the empty index type (the zero space) there are no eigenvalues and the value is the junk `0`; the
ground space is then the zero space either way. Every Hamiltonian of this mission is
`Σ_i θ_i F_i` with real `θ_i` and Hermitian `F_i`. -/
noncomputable def groundEnergy {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) : ℝ :=
  sInf {E : ℝ | Module.End.HasEigenvalue (Matrix.toEuclideanLin H) (E : ℂ)}

end ChenMaxEnt


