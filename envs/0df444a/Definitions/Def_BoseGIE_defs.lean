-- Prove2me | Definitions.Def_BoseGIE_defs
-- name    : BoseGIE_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-11T19:24:16.066289+00:00
-- url     : https://prove2.me/theorems/82d0217c-925e-45f7-b866-4cbfddaac6a3
-- title:
--   Two masses as orbital qubits: the evolved state, product vectors, separability and reduced purity (Bose et al. 2017)
-- statement:
--   Shared vocabulary of the mission. Each mass is an orbital qubit ($0=|L\rangle$, $1=|R\rangle$); two-qubit objects are indexed by pairs $(j,k)$ with mass 1 first. Defines the evolved state $\psi_{\mathrm{End}}(\alpha,\beta)=\tfrac12(|LL\rangle+e^{i\alpha}|LR\rangle+e^{i\beta}|RL\rangle+|RR\rangle)$ (Eq. (2), global phase omitted); product vectors $u\otimes w$; the projector $|v\rangle\langle v|$; the partial trace over mass 2 and the reduced-state purity $\operatorname{Tr}\rho_1^2$; and **separable** states: finite convex combinations $\sum_i p_i\,\rho_i^{(1)}\otimes\rho_i^{(2)}$ of products of density matrices (`PeresTerno.IsDensityMatrix`: PSD, trace one).
-- source:
--   S. Bose et al., A Spin Entanglement Witness for Quantum Gravity, Phys. Rev. Lett. 119, 240401 (2017), https://arxiv.org/abs/1707.06050v1, p. 2, Eqs. (1)–(2)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

/-!
# Gravitationally induced entanglement of two masses

Definitions for the mission drafted from S. Bose, A. Mazumdar, G. W. Morley, H. Ulbricht,
M. Toroš, M. Paternostro, A. A. Geraci, P. F. Barker, M. S. Kim and G. Milburn,
*A Spin Entanglement Witness for Quantum Gravity*, Phys. Rev. Lett. 119, 240401 (2017),
arXiv:1707.06050v1, p. 2, Eqs. (1)–(2).

Each test mass `j = 1, 2` is an "orbital qubit" with basis `|L⟩, |R⟩` (or, on p. 3, the
spin-orbital states `|L,↑⟩, |R,↓⟩`), encoded as `Fin 2` with `0 ↦ |L⟩` and `1 ↦ |R⟩`.
Two-qubit vectors and matrices are indexed by `Qubit × Qubit`, the first component being mass 1.
-/

namespace BoseGIE

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

/-- An orbital qubit: `0 ↦ |L⟩`, `1 ↦ |R⟩`. -/
abbrev Qubit := Fin 2

/-- Eq. (2), global phase `e^{iφ}` omitted: the two-qubit state
`½ (|LL⟩ + e^{iΔφ_LR} |LR⟩ + e^{iΔφ_RL} |RL⟩ + |RR⟩)`, with `α = Δφ_LR` and `β = Δφ_RL`.
The entry at `(j, k)` is the amplitude of mass 1 in `j` and mass 2 in `k`. -/
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

/-- Partial trace over mass 2: `(Tr₂ ρ)_{ij} = ∑ₖ ρ_{(i,k),(j,k)}` (the reduced state of mass 1). -/
def ptrace₂ (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) : Matrix Qubit Qubit ℂ :=
  Matrix.of fun i j => ∑ k, ρ (i, k) (j, k)

/-- The purity `Tr ρ₁²` of the reduced state `ρ₁ = Tr₂ |v⟩⟨v|` of mass 1 (real part). -/
def reducedPurity (v : Qubit × Qubit → ℂ) : ℝ :=
  (ptrace₂ (pureDM v) * ptrace₂ (pureDM v)).trace.re

/-- Separable two-qubit state: a finite convex combination `∑ᵢ pᵢ ρᵢ^{(1)} ⊗ ρᵢ^{(2)}` of
products of density matrices. A state is entangled when it is not separable. -/
def IsSeparable (ρ : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → ℝ) (ρ₁ ρ₂ : Fin n → Matrix Qubit Qubit ℂ),
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
    (∀ i, PeresTerno.IsDensityMatrix (ρ₁ i)) ∧ (∀ i, PeresTerno.IsDensityMatrix (ρ₂ i)) ∧
    ρ = ∑ i, (p i : ℂ) • (ρ₁ i ⊗ₖ ρ₂ i)

end

end BoseGIE


