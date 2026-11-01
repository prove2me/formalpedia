-- Prove2me | Definitions.Def_ChenMaxEnt_groundSpace
-- name    : ChenMaxEnt_groundSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:13.824057+00:00
-- url     : https://prove2.me/theorems/4f022bc2-38f0-47d8-b418-0c0d9e9d3d52
-- title:
--   Ground space $V_0$ of a Hamiltonian
-- statement:
--   Let $H$ be a Hermitian operator on $\mathcal H = \mathbb C^n$ with ground energy $E_0(H)$ (its lowest eigenvalue). The **ground space** (ground-state space) of $H$ is the eigenspace
--
--   $$
--   V_0(H) = \{v \in \mathbb C^n \mid H v = E_0(H)\, v\} .
--   $$
--
--   Its unit vectors are the ground states; its dimension is the ground state degeneracy. $H$ has a **unique ground state** when $\dim V_0(H) = 1$ and is **degenerate** when $\dim V_0(H) > 1$.
--
--   **Formalization Note** A subspace of `EuclideanSpace ℂ n` ($\mathbb C^n$ with its standard inner product), defined as the eigenspace of the matrix acting on $\mathbb C^n$ for the eigenvalue `ChenMaxEnt.groundEnergy H`. It is the eigenspace of the minimum eigenvalue, not the kernel of $H$.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §5.3, Observation 3, p.22 ("the ground state space V0"); Example 4, p.11 ("The ground-state space of H is two-fold degenerate")

import Mathlib
import Definitions.Def_ChenMaxEnt_groundEnergy

namespace ChenMaxEnt

/-- Chen et al., arXiv:1406.5046v2, Observation 3, p.22: "the ground state space V0 of some
Hamiltonian H0"; Example 4, p.11: "The ground-state space of H is two-fold degenerate". The ground
space of a Hamiltonian `H` is the eigenspace of its lowest eigenvalue (`groundEnergy H`); its
unit vectors are the ground states. "Unique ground state" means
`Module.finrank ℂ (groundSpace H) = 1`, and the ground state degeneracy is
`Module.finrank ℂ (groundSpace H)`.

**Formalization Note.** A subspace of `EuclideanSpace ℂ n` (the Hilbert space `ℂ^n` with its
standard inner product), the eigenspace of `Matrix.toEuclideanLin H` for the eigenvalue
`groundEnergy H`. It is the eigenspace of the minimum eigenvalue, not the kernel of `H`. -/
noncomputable def groundSpace {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  Module.End.eigenspace (Matrix.toEuclideanLin H) (groundEnergy H : ℂ)

end ChenMaxEnt


