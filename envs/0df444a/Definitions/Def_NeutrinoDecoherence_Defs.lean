-- Prove2me | Definitions.Def_NeutrinoDecoherence_Defs
-- name    : NeutrinoDecoherence_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T11:29:36.78791+00:00
-- url     : https://prove2.me/theorems/665e7e42-dacf-4a0c-9531-4b2f42bc0658
-- title:
--   Two-level open-system neutrino oscillations: states, entropies, Lindbladian
-- statement:
--   Shared definitions for the mission, all in the namespace `NeutrinoDecoherence`.
--
--   1. **Density matrix.** An $n\times n$ complex matrix $\rho$ is a density matrix if it is positive semidefinite and $\operatorname{Tr}\rho = 1$.
--   2. **Linear entropy** $S_l(\rho) = 1 - \operatorname{Re}\operatorname{Tr}(\rho^2)$ (eq. (2.44)).
--   3. **Von Neumann entropy** $S(\rho) = -\operatorname{Tr}(\rho\ln\rho)$ (eq. (2.39)), computed as $\operatorname{Re}\operatorname{Tr}\,\eta(\rho)$ with $\eta(x) = -x\ln x$ applied by the continuous functional calculus.
--   4. **Relative entropy** $S(\rho\|\sigma) = \operatorname{Tr}(\rho\ln\rho) - \operatorname{Tr}(\rho\ln\sigma)$ (eq. (2.42)), real parts, matrix logarithm by functional calculus.
--   5. **Pauli matrices** $\sigma_1,\sigma_2,\sigma_3$ (eq. (3.3)).
--   6. **Dissipator** (eq. (3.4)) of a $3\times3$ complex **Kossakowski matrix** $a=(a_{ij})$:
--   $$D[\rho] = \frac12\sum_{i,j=1}^{3} a_{ij}\bigl(2\sigma_i\rho\sigma_j - \{\sigma_j\sigma_i,\rho\}\bigr).$$
--   7. **Lindbladian** $\mathcal L[\rho] = -i[H,\rho] + D[\rho]$ (eq. (2.35) with constant coefficients), and the predicate that a curve $t\mapsto\rho(t)$ solves $\dot\rho = \mathcal L[\rho]$ for all $t\ge 0$ (entrywise, one-sided derivative at $t=0$).
--   8. **Two-flavour vacuum Hamiltonian** in the mass basis, $H=\operatorname{diag}(0,\Delta m^2/2E)$ (eq. (3.9)); **mixing matrix** with Majorana phase $\alpha$,
--   $$U=\begin{pmatrix}\cos\theta & e^{i\alpha}\sin\theta\\ -e^{-i\alpha}\sin\theta & \cos\theta\end{pmatrix}$$
--   (eq. (3.13)); the **initial muon-neutrino state** $\rho_\mu(0) = U^\dagger\,|\nu_1\rangle\langle\nu_1|\,U$ (eq. (3.14)).
--   9. **Transition probability** $P = \operatorname{Re}\operatorname{Tr}(\rho_{\text{evolved}}\,\rho_{\text{detected}})$ (eq. (1.11)).
--
--   These objects are the whole model on which every theorem of the mission is stated.
--
--   **Formalization Note** Indices $1,2,3$ of the thesis are `0,1,2` in Lean. The functional calculus returns junk values for non-self-adjoint inputs and reads $\ln 0$ as $0$; the theorems add density-matrix / positive-definiteness hypotheses where this matters. Time evolution is encoded by the differential equation itself rather than by the exponential $e^{\mathcal L t}$ of eq. (2.38).
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; eqs. (1.11), (2.1), (2.35), (2.39), (2.42), (2.44), (3.3), (3.4), (3.9), (3.13), (3.14).

import Mathlib

/-!
# Neutrino oscillations as an open quantum system — definitions

Definition layer for a draft mission proposal based on
G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment*,
Master's dissertation, Instituto de Física, Universidade de São Paulo (2020).

Equation numbers refer to that dissertation.
-/

open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence

/-- A density matrix (eq. (2.1)): positive semidefinite with unit trace. -/
def IsDensityMatrix {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- Linear entropy (eq. (2.44)): `S_l(ρ) = 1 - Tr ρ²`. -/
noncomputable def linearEntropy {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : ℝ :=
  1 - (ρ * ρ).trace.re

/-- Von Neumann entropy (eq. (2.39)): `S(ρ) = -Tr(ρ ln ρ)`, computed through the
continuous functional calculus as `Tr(η(ρ))` with `η(x) = -x ln x` (and `η(0) = 0`). -/
noncomputable def vonNeumannEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : ℝ :=
  (cfc Real.negMulLog ρ).trace.re

/-- Relative entropy (eq. (2.42)): `S(ρ‖σ) = Tr(ρ ln ρ) - Tr(ρ ln σ)`, with the matrix
logarithm taken through the continuous functional calculus (`ln 0` is read as `0`, so this is
only meaningful when `σ` is positive definite). -/
noncomputable def relativeEntropy {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) : ℝ :=
  (ρ * cfc Real.log ρ).trace.re - (ρ * cfc Real.log σ).trace.re

/-- The Pauli matrices `σ₁, σ₂, σ₃` (eq. (3.3)), indexed by `Fin 3`
(index `0 ↦ σ₁`, `1 ↦ σ₂`, `2 ↦ σ₃`). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -I; I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The two-level Dissipator (eq. (3.4)) associated with a Kossakowski matrix `a`
(indices `0,1,2` stand for the thesis' `1,2,3`):
`D[ρ] = ½ ∑_{i,j} a_{ij} (2 σ_i ρ σ_j - {σ_j σ_i, ρ})`. -/
noncomputable def dissipator (a : Matrix (Fin 3) (Fin 3) ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, a i j •
    ((2 : ℂ) • (pauli i * ρ * pauli j) - (pauli j * pauli i * ρ + ρ * (pauli j * pauli i)))

/-- The two-level Lindbladian (eq. (2.35) with constant coefficients):
`L[ρ] = -i [H, ρ] + D[ρ]`. -/
noncomputable def lindbladian (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-I) • (H * ρ - ρ * H) + dissipator a ρ

/-- `ρ : ℝ → M₂(ℂ)` solves the Lindblad equation `dρ/dt = L[ρ]` for all times `t ≥ 0`
(eqs. (2.35), (2.38), (3.8)), expressed entrywise with one-sided derivatives at `t = 0`. -/
def IsLindbladSolution (H : Matrix (Fin 2) (Fin 2) ℂ) (a : Matrix (Fin 3) (Fin 3) ℂ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ i j : Fin 2,
    HasDerivWithinAt (fun s => ρ s i j) (lindbladian H a (ρ t) i j) (Set.Ici 0) t

/-- The two-flavour vacuum Hamiltonian in the mass basis (eq. (3.9)):
`H = diag(0, Δm²/(2E))`. -/
noncomputable def twoFlavourHamiltonian (Δm2 E : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, ((Δm2 / (2 * E) : ℝ) : ℂ)]

/-- The two-flavour mixing matrix with Majorana phase `α` (eq. (3.13)). -/
noncomputable def mixingMatrix (θ α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), exp (α * I) * (Real.sin θ : ℂ);
     -(exp (-(α * I)) * (Real.sin θ : ℂ)), (Real.cos θ : ℂ)]

/-- The initial muon-neutrino state written in the mass basis (eq. (3.14)):
`ρ_μ(0) = U† |ν₁⟩⟨ν₁| U`. -/
noncomputable def muonInitialState (θ α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (mixingMatrix θ α)ᴴ * Matrix.single 0 0 1 * mixingMatrix θ α

/-- Transition probability between an evolved state and a detected pure state
(eq. (1.11)): `P = Tr{ρ_β ρ_α}` (real part). -/
noncomputable def transitionProbability {n : Type*} [Fintype n]
    (ρ_evolved ρ_detected : Matrix n n ℂ) : ℝ :=
  (ρ_evolved * ρ_detected).trace.re

end NeutrinoDecoherence


