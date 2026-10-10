-- Prove2me | Definitions.Def_KochHF_FockSpace
-- name    : KochHF_FockSpace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:22:20.12686+00:00
-- url     : https://prove2.me/theorems/d7e10af2-3a24-4688-b800-ca16f1c344cc
-- title:
--   Second quantization on $K$ orbitals: creators, annihilators, Slater determinants
-- statement:
--   Fix $K$ orthonormal reference orbitals $\phi_0,\dots,\phi_{K-1}$. A one-electron orbital $|\varphi\rangle=\sum_\mu\varphi_\mu|\phi_\mu\rangle$ is identified with its coefficient vector $\varphi\in\mathbb C^K$, with inner product $\langle\varphi|\chi\rangle=\sum_\mu\overline{\varphi_\mu}\,\chi_\mu$.
--
--   The **Fock space** is spanned by the orthonormal occupation-number states $|S\rangle$, $S\subseteq\{0,\dots,K-1\}$, so vectors are functions $\psi:\mathcal P(\{0,\dots,K-1\})\to\mathbb C$ and operators are complex $2^K\times 2^K$ matrices. The definitions are:
--
--   1. **Creation operator** $c_i^\dagger|S\rangle=(-1)^{\#\{j\in S:\ j>i\}}\,|S\cup\{i\}\rangle$ if $i\notin S$, and $c_i^\dagger|S\rangle=0$ if $i\in S$. With this sign convention $c^\dagger_{n_N}\cdots c^\dagger_{n_1}|0\rangle=|\{n_1,\dots,n_N\}\rangle$ for $n_1<\dots<n_N$ (Eq. (26)).
--   2. **Annihilation operator** $c_i=(c_i^\dagger)^\dagger$ (conjugate transpose).
--   3. **Vacuum** $|0\rangle=|\emptyset\rangle$ and basis states $|S\rangle$.
--   4. Inner product $\langle\psi|\varphi\rangle=\sum_S\overline{\psi_S}\varphi_S$ and matrix elements $\langle\psi|A|\varphi\rangle$.
--   5. **Orbital operators** (Eq. (16)): $c^\dagger_\varphi=\sum_\mu\varphi_\mu c^\dagger_\mu$ and $c_\varphi=\sum_\mu\overline{\varphi_\mu}c_\mu$.
--   6. **Slater determinant** (Eqs. (23), (26)) of orbitals $\alpha_1,\dots,\alpha_N$:
--   $$|\Phi_{\alpha_1\cdots\alpha_N}\rangle=c^\dagger_{\alpha_N}\cdots c^\dagger_{\alpha_1}|0\rangle .$$
--   7. **Projection onto the occupied orbitals** (Eq. (41)): $P|\varphi\rangle=\sum_n|\alpha_n\rangle\langle\alpha_n|\varphi\rangle$.
--   8. **One-body operator** (Eqs. (33), (55)): $\hat M=\sum_{a,b}M_{ab}\,c^\dagger_a c_b$ for a $K\times K$ matrix $M$.
--
--   These are the objects in terms of which every statement of the mission is phrased.
--
--   **Formalization Note** Orbitals are indexed $0,\dots,K-1$ (`Fin K`) and the $N$ orbitals of a determinant by `Fin N`; `slater α` applies $c^\dagger_{\alpha_0}$ first. The source works with a possibly infinite orbital basis; here the basis is finite, as in the variational treatment of Sec. 3.
-- source:
--   E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, in E. Pavarini, E. Koch, J. van den Brink, G. Sawatzky (eds.), Quantum Materials: Experiments and Theory, Modeling and Simulation Vol. 6, Forschungszentrum Jülich, 2016, ISBN 978-3-95806-159-0, http://www.cond-mat.de/events/correl16, Sec. 2.1–2.4, pp. 2.5–2.13, Eqs. (14)–(16), (23), (26), (33), (41), (55).

import Mathlib

/-!
# Second quantization on a finite orbital basis

E. Koch, *Mean-Field Theory: Hartree-Fock and BCS*, Sec. 2 (Eqs. (14)-(16), (23), (26), (33), (41)).

Fix `K` orthonormal reference orbitals `ϕ_0, …, ϕ_{K-1}`.  A one-electron orbital is its
coefficient vector `Fin K → ℂ`.  The Fock space has the orthonormal occupation-number basis
`|S⟩`, `S ⊆ {0,…,K-1}`; Fock-space vectors are functions `Finset (Fin K) → ℂ` and operators are
complex matrices indexed by `Finset (Fin K)`.
-/

noncomputable section

namespace KochHF

open Matrix

/-- Vectors in the Fock space over `K` orbitals (coefficients in the occupation-number basis). -/
abbrev FockVec (K : ℕ) := Finset (Fin K) → ℂ

/-- Linear operators on the Fock space over `K` orbitals. -/
abbrev FockOp (K : ℕ) := Matrix (Finset (Fin K)) (Finset (Fin K)) ℂ

/-- Fermion sign `(-1)^{#{j ∈ S : i < j}}`. -/
def fermiSign {K : ℕ} (i : Fin K) (S : Finset (Fin K)) : ℂ :=
  (-1) ^ (S.filter (fun j => i < j)).card

/-- Creation operator `c†_i` of the reference orbital `ϕ_i`:
`c†_i |S⟩ = (-1)^{#{j ∈ S : j > i}} |S ∪ {i}⟩` if `i ∉ S`, and `c†_i |S⟩ = 0` if `i ∈ S`. -/
def cdag {K : ℕ} (i : Fin K) : FockOp K :=
  Matrix.of fun T S => if i ∉ S ∧ T = insert i S then fermiSign i S else 0

/-- Annihilation operator `c_i`, the adjoint (conjugate transpose) of `c†_i`. -/
def cann {K : ℕ} (i : Fin K) : FockOp K := (cdag i)ᴴ

/-- The vacuum state `|0⟩` (no orbital occupied). -/
def vacuum (K : ℕ) : FockVec K := Pi.single ∅ 1

/-- The occupation-number basis state `|S⟩`. -/
def basisState {K : ℕ} (S : Finset (Fin K)) : FockVec K := Pi.single S 1

/-- Fock-space inner product `⟨ψ|φ⟩ = Σ_S conj(ψ_S) φ_S`. -/
def fockInner {K : ℕ} (ψ φ : FockVec K) : ℂ := star ψ ⬝ᵥ φ

/-- Matrix element `⟨ψ|A|φ⟩`. -/
def matEl {K : ℕ} (ψ : FockVec K) (A : FockOp K) (φ : FockVec K) : ℂ := star ψ ⬝ᵥ (A *ᵥ φ)

/-- One-electron inner product `⟨φ|χ⟩ = Σ_μ conj(φ_μ) χ_μ`. -/
def orbInner {K : ℕ} (φ χ : Fin K → ℂ) : ℂ := star φ ⬝ᵥ χ

/-- Creation operator of the orbital `|φ⟩ = Σ_μ φ_μ |ϕ_μ⟩`: `c†_φ = Σ_μ φ_μ c†_μ` (Eq. (16)). -/
def cdagOrb {K : ℕ} (φ : Fin K → ℂ) : FockOp K := ∑ μ, φ μ • cdag μ

/-- Annihilation operator of the orbital `|φ⟩`: `c_φ = Σ_μ conj(φ_μ) c_μ`. -/
def cannOrb {K : ℕ} (φ : Fin K → ℂ) : FockOp K := ∑ μ, star (φ μ) • cann μ

/-- The Slater determinant `c†_{α_N} ⋯ c†_{α_1} |0⟩` of the orbitals `α_1, …, α_N`
(Eqs. (23), (26)); the orbitals are indexed `α 0, …, α (N-1)` and `c†_{α 0}` acts first. -/
def slater {K N : ℕ} (α : Fin N → Fin K → ℂ) : FockVec K :=
  (List.ofFn fun n => cdagOrb (α n)).reverse.prod *ᵥ vacuum K

/-- `P|φ⟩ = Σ_n |α_n⟩⟨α_n|φ⟩`, the projection onto the occupied orbitals (Eq. (41)). -/
def occProj {K N : ℕ} (α : Fin N → Fin K → ℂ) (φ : Fin K → ℂ) : Fin K → ℂ :=
  ∑ n, orbInner (α n) φ • α n

/-- Second-quantized one-body operator `M̂ = Σ_{a,b} M_{ab} c†_a c_b` (Eqs. (33), (55)). -/
def oneBodyOp {K : ℕ} (M : Matrix (Fin K) (Fin K) ℂ) : FockOp K :=
  ∑ a, ∑ b, M a b • (cdag a * cann b)

end KochHF

end


