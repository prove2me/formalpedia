-- Prove2me | Definitions.Def_BMV2017_defs
-- name    : BMV2017_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-08T23:53:23.98218+00:00
-- url     : https://prove2.me/theorems/ec7bc8e4-ded7-4a4d-a32c-f0e868ac4314
-- title:
--   Two-qubit states, separability and the spin entanglement witness (Bose et al. 2017)
-- statement:
--   Shared vocabulary of the mission. Each test mass carries a qubit ($|0\rangle=|L\rangle$ or $|{\uparrow}\rangle$, $|1\rangle=|R\rangle$ or $|{\downarrow}\rangle$); two-qubit objects are indexed with mass 1 first. Defines the Pauli matrices; the evolved state $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12(|00\rangle+e^{i\alpha}|01\rangle+e^{i\beta}|10\rangle+|11\rangle)$ (Eq. (2), spin form on p. 3, global phase omitted); product vectors; $|v\rangle\langle v|$; the partial trace over mass 2 and the reduced-state purity $\operatorname{Tr}\rho_1^2$; **separable** states (finite convex combinations of products of density matrices); the witness $\mathcal W(\rho)=|\operatorname{Tr}\rho(\sigma_x\otimes\sigma_z)-\operatorname{Tr}\rho(\sigma_y\otimes\sigma_y)|$ (p. 3); and its variant with each spin's operators conjugated by $\operatorname{diag}(1,e^{i\theta})$ (p. 4).
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2 Eqs. (1)–(2); p. 3 (spin state and witness W); p. 4

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

/-!
# The spin entanglement witness for quantum gravity

Definitions for the mission drafted from S. Bose, A. Mazumdar, G. W. Morley, H. Ulbricht,
M. Toroš, M. Paternostro, A. A. Geraci, P. F. Barker, M. S. Kim and G. Milburn,
*A Spin Entanglement Witness for Quantum Gravity*, Phys. Rev. Lett. 119, 240401 (2017),
arXiv:1707.06050v1.

Each test mass `j = 1, 2` carries a qubit: the orbital states `|L⟩, |R⟩` (Eqs. (1)–(2)),
or after the Stern–Gerlach interferometry the spin states `|↑⟩, |↓⟩` (p. 3). Both are encoded
as `Fin 2` with `0 ↦ |L⟩ / |↑⟩` and `1 ↦ |R⟩ / |↓⟩`. Two-qubit vectors and matrices are
indexed by `Qubit × Qubit`, the first component being mass 1.
-/

namespace BMV2017

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

/-- A qubit: `0 ↦ |L⟩` (or `|↑⟩`), `1 ↦ |R⟩` (or `|↓⟩`). -/
abbrev Qubit := Fin 2

/-- Pauli matrix `σ_x`. -/
def σx : Matrix Qubit Qubit ℂ := !![0, 1; 1, 0]

/-- Pauli matrix `σ_y`. -/
def σy : Matrix Qubit Qubit ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix `σ_z` (`|↑⟩` has eigenvalue `+1`). -/
def σz : Matrix Qubit Qubit ℂ := !![1, 0; 0, -1]

/-- Eq. (2) (and the spin state on p. 3, overall phase omitted): the two-qubit state
`½ (|00⟩ + e^{iΔφ_LR} |01⟩ + e^{iΔφ_RL} |10⟩ + |11⟩)`, with `α = Δφ_LR` and `β = Δφ_RL`. -/
def psiEnd (α β : ℝ) : Qubit × Qubit → ℂ :=
  fun p => (1 / 2 : ℂ) *
    (!![1, Complex.exp (α * Complex.I); Complex.exp (β * Complex.I), 1] : Matrix Qubit Qubit ℂ)
      p.1 p.2

/-- A two-qubit vector factorizes as `u ⊗ w`. -/
def IsProductVector (v : Qubit × Qubit → ℂ) : Prop :=
  ∃ u w : Qubit → ℂ, ∀ i j, v (i, j) = u i * w j

/-- The density matrix `|v⟩⟨v|` of a vector `v`. -/
def pureDM (v : Qubit × Qubit → ℂ) : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ :=
  Matrix.of fun p q => v p * star (v q)

/-- Partial trace over the second qubit: `(Tr₂ ρ)_{ij} = ∑ₖ ρ_{(i,k),(j,k)}`
(the reduced state of mass 1). -/
def ptrace₂ (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) : Matrix Qubit Qubit ℂ :=
  Matrix.of fun i j => ∑ k, ρ (i, k) (j, k)

/-- The purity `Tr ρ₁²` of the reduced state `ρ₁ = Tr₂ |v⟩⟨v|` of mass 1 (real part). -/
def reducedPurity (v : Qubit × Qubit → ℂ) : ℝ :=
  (ptrace₂ (pureDM v) * ptrace₂ (pureDM v)).trace.re

/-- Separable two-qubit state: a finite convex combination `∑ᵢ pᵢ ρᵢ^{(1)} ⊗ ρᵢ^{(2)}` of
products of density matrices. -/
def IsSeparable (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (ρ₁ ρ₂ : Fin n → Matrix Qubit Qubit ℂ),
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
    (∀ i, PeresTerno.IsDensityMatrix (ρ₁ i)) ∧ (∀ i, PeresTerno.IsDensityMatrix (ρ₂ i)) ∧
    ρ = ∑ i, (p i : ℂ) • (ρ₁ i ⊗ₖ ρ₂ i)

/-- p. 3: the entanglement witness
`𝒲(ρ) = |⟨σ_x^{(1)} ⊗ σ_z^{(2)}⟩ − ⟨σ_y^{(1)} ⊗ σ_y^{(2)}⟩|`, with `⟨O⟩ = Tr(ρ O)`. -/
def witness (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) : ℝ :=
  ‖(ρ * (σx ⊗ₖ σz)).trace - (ρ * (σy ⊗ₖ σy)).trace‖

/-- The local phase rotation `diag(1, e^{iθ})` of one spin. -/
def phaseRot (θ : ℝ) : Matrix Qubit Qubit ℂ := !![1, 0; 0, Complex.exp (θ * Complex.I)]

/-- p. 4: the witness with each spin's operators readjusted by a local phase rotation,
`σ ↦ R(θ)† σ R(θ)` with `R(θ) = diag(1, e^{iθ})` (`θ₁` for mass 1, `θ₂` for mass 2):
`|⟨σ_x^{θ₁} ⊗ σ_z^{θ₂}⟩ − ⟨σ_y^{θ₁} ⊗ σ_y^{θ₂}⟩|`. With `θ₁ = θ₂ = 0` it is `witness`. -/
def witnessRot (θ₁ θ₂ : ℝ) (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) : ℝ :=
  ‖(ρ * (((phaseRot θ₁)ᴴ * σx * phaseRot θ₁) ⊗ₖ ((phaseRot θ₂)ᴴ * σz * phaseRot θ₂))).trace -
    (ρ * (((phaseRot θ₁)ᴴ * σy * phaseRot θ₁) ⊗ₖ ((phaseRot θ₂)ᴴ * σy * phaseRot θ₂))).trace‖

end

end BMV2017


