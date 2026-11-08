-- Prove2me | Definitions.Def_SingleInteraction_energy
-- name    : SingleInteraction_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:29.822882+00:00
-- url     : https://prove2.me/theorems/05f3069d-e0bc-4e3a-b2c9-5ef62a2cc1df
-- title:
--   Energy $\langle\phi|A|\phi\rangle$ of a state
-- statement:
--   For an operator $A$ on a finite-dimensional register and a vector $|\phi\rangle$, the energy of $|\phi\rangle$ is $\langle\phi|A|\phi\rangle$. The promise of every Hamiltonian problem in the mission is phrased through it, over normalized states.
--
--   **Formalization Note** The value is the real part of $\langle\phi,A\phi\rangle$, which is the whole expectation value for Hermitian $A$ (the only case used).
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 6, p.18; Definition 31, p.30

import Mathlib

namespace SingleInteraction

/-- The energy `⟨ϕ| A |ϕ⟩` of a state `ϕ` with respect to an operator `A` on a finite-dimensional
register (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 6, p.18, and Definition 31, p.30: "`⟨ϕ| H |ϕ⟩ ≤ a`").

**Formalization Note** States are vectors of `EuclideanSpace ℂ ι`; the inner product is conjugate-linear
in its first argument. The value is the real part of `⟨ϕ, Aϕ⟩`, which is the whole expectation value
when `A` is Hermitian (the only case used). Normalization `‖ϕ‖ = 1` is imposed where states are
quantified. -/
noncomputable def energy {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (φ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ φ (Matrix.toEuclideanLin A φ)).re

end SingleInteraction


