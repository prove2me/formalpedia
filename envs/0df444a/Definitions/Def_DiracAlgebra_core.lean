-- Prove2me | Definitions.Def_DiracAlgebra_core
-- name    : DiracAlgebra_core
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T19:35:59.491567+00:00
-- url     : https://prove2.me/theorems/0a83d3a0-4309-487e-b776-e05f92760d5c
-- title:
--   Gamma matrices: the Clifford relation $\{\gamma^\mu,\gamma^\nu\}=2\eta^{\mu\nu}I_4$, the Dirac representation, and the Feynman slash
-- statement:
--   The algebraic layer of the Dirac equation, in $3+1$ dimensional Minkowski spacetime with the
--   mainly-negative metric $\eta^{\mu\nu} = \operatorname{diag}(1,-1,-1,-1)$.
--
--   A quadruple $\gamma = (\gamma^0,\gamma^1,\gamma^2,\gamma^3)$ of complex $4\times4$ matrices is a
--   **family of gamma matrices** when it satisfies the defining relation of the Dirac (Clifford)
--   algebra,
--
--   $$\{\gamma^\mu,\gamma^\nu\} = \gamma^\mu\gamma^\nu + \gamma^\nu\gamma^\mu = 2\eta^{\mu\nu} I_4 ,
--   \qquad \mu,\nu \in \{0,1,2,3\},$$
--
--   where $I_4$ is the identity matrix. The relation does not single out the matrices; the
--   **Dirac representation** is the standard concrete solution
--
--   $$\gamma^0 = \begin{pmatrix} I_2 & 0 \\ 0 & -I_2\end{pmatrix}, \qquad
--   \gamma^i = \begin{pmatrix} 0 & \sigma_i \\ -\sigma_i & 0\end{pmatrix}, \quad i = 1,2,3,$$
--
--   with $\sigma_1,\sigma_2,\sigma_3$ the Pauli matrices, and it is recorded here entrywise as four
--   explicit $4\times4$ matrices.
--
--   For a covector $p = (p_\mu)$ with complex entries the **Feynman slash** is the matrix
--   $p\!\!\!/ = \gamma^\mu p_\mu = \sum_{\mu=0}^{3} p_\mu \gamma^\mu$. Finally, the matrices of the
--   Hamiltonian form of the Dirac equation are $\beta = \gamma^0$ and $\alpha^i = \gamma^0\gamma^i$,
--   both taken in the Dirac representation.
--
--   This bundle is the foundation every other statement of the mission is phrased in: the gamma
--   family predicate is the hypothesis of the representation-independent results, and the explicit
--   Dirac representation is what the concrete computations are about.
--
--   **Formalization Note.** Spacetime indices range over `Fin 4`; the metric is complex-valued so
--   that it can be multiplied directly with matrix entries; the three Pauli matrices are indexed by
--   `Fin 3`, and the spatial gamma index $i$ of $\alpha^i$ is obtained from that index by `Fin.succ`.
-- source:
--   "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation).

import Mathlib

namespace DiracEquation

open Matrix

/-- The Minkowski metric `η^{μν} = diag(1, -1, -1, -1)` in the mainly-negative signature,
with complex entries. -/
def eta (mu nu : Fin 4) : ℂ := if mu = nu then (if mu = 0 then 1 else -1) else 0

/-- `IsGammaFamily g` says that the four `4 × 4` complex matrices `g 0, g 1, g 2, g 3` satisfy
the defining relation of the Dirac algebra, `{γ^μ, γ^ν} = 2 η^{μν} I₄`. -/
def IsGammaFamily (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ mu nu, g mu * g nu + g nu * g mu = (2 * eta mu nu) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The Feynman slash `p̸ = γ^μ p_μ` of a covector `p` with respect to a family `g` of gamma
matrices. -/
noncomputable def slash (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (p : Fin 4 → ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ mu, p mu • g mu

/-- The three Pauli matrices `σ₁, σ₂, σ₃` (indexed by `0, 1, 2`). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The gamma matrices in the Dirac representation:
`γ⁰ = [[I₂, 0], [0, -I₂]]` and `γⁱ = [[0, σᵢ], [-σᵢ, 0]]`, written out entrywise. -/
def gammaDirac : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ
  | 0 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]
  | 1 => !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  | 2 => !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0; 0, Complex.I, 0, 0; -Complex.I, 0, 0, 0]
  | 3 => !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]

/-- The Dirac-representation matrix `β = γ⁰` of the Hamiltonian form of the Dirac equation. -/
def betaDirac : Matrix (Fin 4) (Fin 4) ℂ := gammaDirac 0

/-- The Dirac-representation matrices `αⁱ = γ⁰ γⁱ` of the Hamiltonian form of the Dirac
equation (`i = 1, 2, 3`, indexed by `Fin 3` through `Fin.succ`). -/
noncomputable def alphaDirac (i : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  gammaDirac 0 * gammaDirac i.succ

end DiracEquation


