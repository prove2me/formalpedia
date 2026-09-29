-- Prove2me | Definitions.Def_QED_dirac_algebra
-- name    : QED_dirac_algebra
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T03:42:38.777991+00:00
-- url     : https://prove2.me/theorems/cba7e2e0-db36-43dc-b575-a5f7a62f5538
-- title:
--   Dirac matrices: the Clifford relation, the Dirac basis, and the pairing $\bar\psi M \chi$
-- statement:
--   The algebraic layer. A family $\gamma=(\gamma^0,\gamma^1,\gamma^2,\gamma^3)$ of complex $4\times4$ matrices is a **Dirac representation** for the metric $\eta=\mathrm{diag}(1,-1,-1,-1)$ when it satisfies the Clifford anticommutation relation
--   $$\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\eta^{\mu\nu}I_4$$
--   together with the hermiticity relation $(\gamma^\mu)^\dagger=\gamma^0\gamma^\mu\gamma^0$, which says that $\gamma^0$ is hermitian and $\gamma^1,\gamma^2,\gamma^3$ are anti-hermitian. These two properties are exactly what the Dirac theory uses: the first makes the Dirac operator a square root of the wave operator, the second makes the Dirac adjoint behave correctly under conjugation.
--
--   The **Dirac basis** is the standard concrete solution of these relations, given explicitly. Finally, for a matrix $M$ the **Dirac pairing** of two spinors is
--   $$\bar\varphi M\chi=\sum_{i,j}\overline{\varphi_i}\,(\gamma^0M)_{ij}\,\chi_j,$$
--   i.e. $\varphi^\dagger\gamma^0M\chi$, the sesquilinear form through which every bilinear quantity of the theory — the current, the mass term, the kinetic term — is expressed.
-- source:
--   Wikipedia, "Quantum electrodynamics", section "Mathematical formulation", subsections "QED action" and "Equations of motion" (QED Lagrangian, Dirac matrices, covariant derivative, field tensor, conserved current, Euler-Lagrange equations for psi and A, Lorenz-gauge wave equation). https://en.wikipedia.org/wiki/Quantum_electrodynamics

import Definitions.Def_QED_minkowski_spacetime

namespace QED

/-- `IsDiracRepresentation γ` says that the four complex `4 × 4` matrices
`γ 0, γ 1, γ 2, γ 3` are Dirac matrices for the metric `η` with signature
`(+, -, -, -)`:

* the Clifford (anticommutation) relation `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} I₄`;
* the hermiticity relation `(γ^μ)† = γ^0 γ^μ γ^0`,
  i.e. `γ^0` is hermitian and `γ^1, γ^2, γ^3` are anti-hermitian. -/
def IsDiracRepresentation (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  (∀ μ ν : Fin 4,
      γ μ * γ ν + γ ν * γ μ = (2 * (minkowski μ ν : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ∧
  (∀ μ : Fin 4, (γ μ).conjTranspose = γ 0 * γ μ * γ 0)

/-- The gamma matrices in the standard Dirac basis. -/
def diracGamma : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | ⟨0, _⟩ => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
  | ⟨1, _⟩ => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  | ⟨2, _⟩ => !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0;
                 0, Complex.I, 0, 0; -Complex.I, 0, 0, 0]
  | ⟨3, _⟩ => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

/-- The Dirac adjoint pairing `ψ̄ M χ = ψ† γ^0 M χ` of two spinors, for a
`4 × 4` matrix `M` inserted between them. -/
def diracPairing (γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (φ χ : Fin 4 → ℂ) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (starRingEnd ℂ) (φ i) * ((γ 0 * M) i j) * χ j

end QED


