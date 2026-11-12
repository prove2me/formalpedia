-- Prove2me | Definitions.Def_QubitTracking_Bits
-- name    : QubitTracking_Bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:26:34.751825+00:00
-- url     : https://prove2.me/theorems/9aff584c-c005-4b23-8002-5a265fc567ce
-- title:
--   Qubit registers, states, Hadamard and Pauli strings, $n$ EPR pairs, fidelity, Kraus families and trace distance
-- statement:
--   A register of qubits indexed by a finite set $\iota$ has computational-basis labels $\mathrm{Bits}(\iota)=\mathbb F_2^{\iota}$. A pure state is a vector $\psi:\mathbb F_2^{\iota}\to\mathbb C$ and an operator a matrix indexed by $\mathbb F_2^{\iota}$. This module fixes the elementary objects used throughout:
--
--   1. the uniform average $\mathbb E_\omega f(\omega)=|\Omega|^{-1}\sum_\omega f(\omega)$ over a finite sample space, and over a finite set;
--   2. the squared norm $\|\psi\|^2$, the inner product $\langle\varphi,\psi\rangle$ and the rank-one operator $|\psi\rangle\langle\psi|$;
--   3. the Hadamard transform $\langle x|H^{\otimes k}|y\rangle=2^{-k/2}(-1)^{\langle x,y\rangle}$;
--   4. the Pauli strings $\sigma_X(a)|x\rangle=|x+a\rangle$ and $\sigma_Z(a)|x\rangle=(-1)^{\langle a,x\rangle}|x\rangle$ on $n$ qubits;
--   5. $n$ EPR pairs $|\mathrm{EPR}\rangle^{\otimes n}=2^{-n/2}\sum_x|x\rangle|x\rangle$, the $j$-th qubit of the first register paired with the $j$-th qubit of the second;
--   6. the fidelity $F(|\psi\rangle\langle\psi|,\rho)=\mathrm{Re}\,\langle\psi|\rho|\psi\rangle$ with a pure state;
--   7. effects $0\le P\le 1$, Kraus families $\sum_j K_j^\dagger K_j\le 1$ (completely positive, trace non-increasing), isometries $V^\dagger V=1$;
--   8. the statement $\mathrm{TD}(\rho,\sigma)\le\varepsilon$ in its operational form: $|\mathrm{Re}\,\mathrm{Tr}(P(\rho-\sigma))|\le\varepsilon$ for every effect $P$;
--   9. the encoding of $\mathbb F_2^m\cup\{\bot\}$ in $m+1$ qubits, $y\mapsto(y,0)$, $\bot\mapsto(0^m,1)$.
--
--   These are the shared vocabulary of every statement of the mission.
--
--   **Formalization Note** The fidelity is the squared convention $\langle\psi|\rho|\psi\rangle$ of the paper's Definition 8.1 and Theorem 7.9. For density matrices, the operational form of the trace distance is equivalent to the usual one (Helstrom).
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), §3.1, §4 (p.26), Definition 8.1 (p.56), Theorem 7.9 (p.55), Construction 9.5 (p.65)

import Mathlib

set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace QubitTracking

/-- Computational-basis labels of a register of qubits indexed by `ι`: an assignment of a bit
(an element of `𝔽₂ = ZMod 2`) to each qubit. A pure state of the register is a vector
`Bits ι → ℂ` (unnormalized unless stated), a mixed state or operator a matrix indexed by `Bits ι`.

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time (Or:
Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), §3.1 and §4, p.21
and p.26 ("we consider vectors and matrices with elements in `𝔽₂`").

**Formalization Note** States are kept as plain coordinate vectors and matrices over the
computational basis; every register is finite. -/
abbrev Bits (ι : Type*) := ι → ZMod 2

/-- The sign `(-1)^z` of a bit `z ∈ 𝔽₂`, as a complex number. -/
noncomputable def sgn (z : ZMod 2) : ℂ := (-1 : ℂ) ^ z.val

/-- The uniform average `𝔼_{ω} f(ω)` of a real function over a finite sample space (the uniform
distribution on `Ω`). -/
noncomputable def avg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

/-- The uniform average of a complex-matrix-valued function over a finite sample space. -/
noncomputable def avgMat {Ω κ : Type*} [Fintype Ω] (f : Ω → Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  ((Fintype.card Ω : ℂ)⁻¹) • ∑ ω, f ω

/-- The uniform average of a real function over a finite set `s` (the uniform distribution on
`s`; used for sampling from a set such as `CS(A)` in Remark 4.1, p.26). -/
noncomputable def avgOn {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ a ∈ s, f a

/-- The squared Euclidean norm `‖ψ‖² = ∑ |ψ(b)|²` of a state vector. -/
noncomputable def normSq {β : Type*} [Fintype β] (ψ : β → ℂ) : ℝ :=
  ∑ b, Complex.normSq (ψ b)

/-- The inner product `⟨φ, ψ⟩ = ∑ conj(φ(b)) ψ(b)` (antilinear in the first argument). -/
noncomputable def inner' {β : Type*} [Fintype β] (φ ψ : β → ℂ) : ℂ :=
  ∑ b, star (φ b) * ψ b

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
noncomputable def proj {β : Type*} (ψ : β → ℂ) : Matrix β β ℂ :=
  fun a b => ψ a * star (ψ b)

/-- The `k`-qubit Hadamard transform `H^{⊗k}`, `⟨x|H^{⊗k}|y⟩ = 2^{-k/2} (-1)^{⟨x,y⟩}` (p.26:
`|+⟩ ↦ 0`, `|−⟩ ↦ 1` on each coordinate). -/
noncomputable def hadamard (ι : Type*) [Fintype ι] : Matrix (Bits ι) (Bits ι) ℂ :=
  fun x y => ((Real.sqrt 2 : ℂ) ^ Fintype.card ι)⁻¹ * sgn (x ⬝ᵥ y)

/-- The Pauli string `σ_X(a) = σ_X^{a₁} ⊗ ⋯ ⊗ σ_X^{aₙ}` on `n` qubits (p.53): it maps the basis
vector `|x⟩` to `|x + a⟩`. -/
def sigmaX {n : ℕ} (a : Bits (Fin n)) : Matrix (Bits (Fin n)) (Bits (Fin n)) ℂ :=
  fun x y => if x = y + a then 1 else 0

/-- The Pauli string `σ_Z(a) = σ_Z^{a₁} ⊗ ⋯ ⊗ σ_Z^{aₙ}` on `n` qubits (p.53): it multiplies the
basis vector `|x⟩` by `(-1)^{⟨a,x⟩}`. -/
noncomputable def sigmaZ {n : ℕ} (a : Bits (Fin n)) : Matrix (Bits (Fin n)) (Bits (Fin n)) ℂ :=
  fun x y => if x = y then sgn (a ⬝ᵥ x) else 0

/-- `n` EPR pairs `|EPR⟩^{⊗n}`, `|EPR⟩ = (|00⟩ + |11⟩)/√2`, on a pair of `n`-qubit registers, the
`j`-th qubit of the first register paired with the `j`-th qubit of the second:
`|EPR⟩^{⊗n} = 2^{-n/2} ∑_x |x⟩|x⟩` (Theorem 9.6, p.66; Definition 8.1, p.56). -/
noncomputable def eprVec (n : ℕ) : Bits (Fin n) × Bits (Fin n) → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℂ) ^ n)⁻¹ else 0

/-- The fidelity of a (possibly unnormalized) operator `ρ` with a pure state `ψ`:
`F(|ψ⟩⟨ψ|, ρ) = Re ⟨ψ|ρ|ψ⟩` (Definition 8.1, p.56 and Theorem 7.9, p.55).

**Formalization Note** This is the squared-fidelity convention `⟨ψ|ρ|ψ⟩` used in the paper's
Definition 8.1 and Theorem 7.9; it is the smaller (stronger) of the two common conventions. -/
noncomputable def fidPure {β : Type*} [Fintype β] (ψ : β → ℂ) (ρ : Matrix β β ℂ) : ℝ :=
  (inner' ψ (ρ *ᵥ ψ)).re

/-- An effect (a POVM element): a matrix `P` with `0 ≤ P ≤ 1` in the Loewner order. -/
def IsEffect {β : Type*} [Fintype β] [DecidableEq β] (P : Matrix β β ℂ) : Prop :=
  P.PosSemidef ∧ (1 - P).PosSemidef

/-- A finite family of Kraus operators `K_j : ℂ^β → ℂ^γ` with `∑_j K_j† K_j ≤ 1`: a completely
positive trace-non-increasing map (the success branch of an instrument). -/
def IsKrausFamily {r : ℕ} {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ]
    (K : Fin r → Matrix γ β ℂ) : Prop :=
  (1 - ∑ j, (K j)ᴴ * K j).PosSemidef

/-- An isometry `V : ℂ^β → ℂ^γ`, `V†V = 1`. -/
def IsIsometry {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] (V : Matrix γ β ℂ) : Prop :=
  Vᴴ * V = 1

/-- `TDLe ρ σ ε`: the trace distance of `ρ` and `σ` is at most `ε`, in its operational form: no
two-outcome measurement distinguishes them with advantage more than `ε`, i.e.
`|Re Tr(P(ρ - σ))| ≤ ε` for every effect `0 ≤ P ≤ 1`.

**Formalization Note** For density matrices this is equivalent to `TD(ρ, σ) ≤ ε` (Helstrom); the
operational form avoids a supremum. -/
def TDLe {β : Type*} [Fintype β] [DecidableEq β] (ρ σ : Matrix β β ℂ) (ε : ℝ) : Prop :=
  ∀ P : Matrix β β ℂ, IsEffect P → |(P * (ρ - σ)).trace.re| ≤ ε

/-- The encoding of `𝔽₂^m ∪ {⊥}` in `m + 1` qubits (the output of an oracle that may answer `⊥`, Construction 9.5, p.65): `y ↦ (y, 0)`, `⊥ ↦ (0^m, 1)`. -/
def encOpt {m : ℕ} : Option (Bits (Fin m)) → Bits (Fin (m + 1))
  | some y => fun i => if h : (i : ℕ) < m then y ⟨i, h⟩ else 0
  | none => fun i => if (i : ℕ) < m then 0 else 1

end QubitTracking


