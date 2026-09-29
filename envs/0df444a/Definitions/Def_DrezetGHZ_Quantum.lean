-- Prove2me | Definitions.Def_DrezetGHZ_Quantum
-- name    : DrezetGHZ_Quantum
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-28T18:57:43.159984+00:00
-- url     : https://prove2.me/theorems/9be53170-bb44-4f19-8785-ba8d3e085d94
-- title:
--   GHZ scenario: Pauli matrices, GHZ state, spin eigenvectors, Born probabilities
-- statement:
--   Quantum-mechanical objects of the three-particle GHZ experiment.
--
--   1. **Pauli matrices** in the $\sigma_z$ eigenbasis $(|{+z}\rangle,|{-z}\rangle)$:
--   $$\sigma_x=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad \sigma_z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--   2. **Three-qubit operators** $A^{(1)}B^{(2)}C^{(3)} = A\otimes B\otimes C$, acting on vectors indexed by $\{0,1\}^3$ (index $0$ is $|{+z}\rangle$).
--   3. **GHZ state** (Eq. (1)):
--   $$|\psi\rangle=\tfrac{1}{\sqrt2}\big(|{+z}{+z}{+z}\rangle-|{-z}{-z}{-z}\rangle\big).$$
--   4. **Settings** $\hat n\in\{\hat x,\hat y\}$, with observables $\sigma_{\hat x}=\sigma_x$ and $\sigma_{\hat y}=\sigma_y$. The normalized eigenvectors for an outcome $a\in\{\pm1\}$ are
--   $$|a_{\hat x}\rangle=\tfrac1{\sqrt2}(|{+z}\rangle+a|{-z}\rangle),\qquad |a_{\hat y}\rangle=\tfrac1{\sqrt2}(|{+z}\rangle+ia|{-z}\rangle).$$
--   5. **Born probabilities** (Eq. (16) with $\theta=\psi$):
--   $$P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2,\hat n_3,\psi)=\big|\langle\alpha_{\hat n_1}\beta_{\hat n_2}\gamma_{\hat n_3}\mid\psi\rangle\big|^2.$$
--
--   These are the quantum predictions that every GHZ statement in this mission refers to.
--
--   **Formalization Note** Outcomes $\pm1$ are elements of `ℤˣ`. Three-qubit vectors are functions on `Fin 2 × Fin 2 × Fin 2`. `bornProb` is real-valued (`Complex.normSq`).
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, p. 2 Eq. (1); p. 3 Eqs. (2)–(5); p. 5 Eq. (16).

import Mathlib

/-!
# Quantum side of the GHZ scenario (Drezet 2023, Section II, Eqs. (1)–(5))

Qubit basis convention: index `0` is `|+z⟩`, index `1` is `|−z⟩`.
Three-qubit vectors are functions on `Fin 2 × Fin 2 × Fin 2`
(particle 1, particle 2, particle 3); three-qubit operators are threefold
Kronecker products `A ⊗ B ⊗ C`.
-/

namespace DrezetGHZ

open Matrix Kronecker

/-- Pauli matrix `σ_x` in the `σ_z` eigenbasis `(|+z⟩, |−z⟩)`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli matrix `σ_y` in the `σ_z` eigenbasis `(|+z⟩, |−z⟩)`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix `σ_z` in its own eigenbasis `(|+z⟩, |−z⟩)`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Index type of the computational basis of three spin-½ particles. -/
abbrev ThreeQubit := Fin 2 × Fin 2 × Fin 2

/-- The operator `A^{(1)} B^{(2)} C^{(3)} = A ⊗ B ⊗ C` on three qubits. -/
def tensor3 (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix ThreeQubit ThreeQubit ℂ :=
  A ⊗ₖ (B ⊗ₖ C)

/-- The GHZ state of Eq. (1):
`|ψ⟩ = (|+z⟩|+z⟩|+z⟩ − |−z⟩|−z⟩|−z⟩)/√2`. -/
noncomputable def ghzState : ThreeQubit → ℂ := fun i =>
  if i = (0, 0, 0) then 1 / (Real.sqrt 2 : ℂ)
  else if i = (1, 1, 1) then -1 / (Real.sqrt 2 : ℂ)
  else 0

/-- The two Stern–Gerlach settings used in the GHZ argument: spin along `x̂` or along `ŷ`. -/
inductive Setting
  | x
  | y
  deriving DecidableEq

instance : Fintype Setting :=
  ⟨{.x, .y}, fun s => by cases s <;> simp⟩

/-- The spin observable measured for a setting: `σ_x` for `x̂`, `σ_y` for `ŷ`. -/
def Setting.observable : Setting → Matrix (Fin 2) (Fin 2) ℂ
  | .x => pauliX
  | .y => pauliY

/-- Normalized eigenvector of the setting's observable for eigenvalue `a = ±1`
(outcomes are elements of `ℤˣ = {1, -1}`):
`|a_x⟩ = (|+z⟩ + a|−z⟩)/√2`, `|a_y⟩ = (|+z⟩ + i a|−z⟩)/√2`. -/
noncomputable def spinEigenvector : Setting → ℤˣ → (Fin 2 → ℂ)
  | .x, a => ![1 / (Real.sqrt 2 : ℂ), ((a : ℤ) : ℂ) / (Real.sqrt 2 : ℂ)]
  | .y, a => ![1 / (Real.sqrt 2 : ℂ), ((a : ℤ) : ℂ) * Complex.I / (Real.sqrt 2 : ℂ)]

/-- Product vector `|u⟩₁|v⟩₂|w⟩₃`. -/
def productKet (u v w : Fin 2 → ℂ) : ThreeQubit → ℂ := fun i => u i.1 * v i.2.1 * w i.2.2

/-- Born probability `P(α, β, γ | n̂₁, n̂₂, n̂₃, ψ) = |⟨α_{n̂₁}, β_{n̂₂}, γ_{n̂₃} | ψ⟩|²`
(Eq. (16) with `θ = ψ`) that Alice, Bob and Charlie, measuring the GHZ state
along settings `n₁, n₂, n₃`, obtain outcomes `α, β, γ ∈ {±1}`. -/
noncomputable def bornProb (n₁ n₂ n₃ : Setting) (α β γ : ℤˣ) : ℝ :=
  Complex.normSq
    (star (productKet (spinEigenvector n₁ α) (spinEigenvector n₂ β) (spinEigenvector n₃ γ))
      ⬝ᵥ ghzState)

end DrezetGHZ


