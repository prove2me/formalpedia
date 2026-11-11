-- Prove2me | Definitions.Def_QFairEx_SupportedOn
-- name    : QFairEx_SupportedOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:00.589389+00:00
-- url     : https://prove2.me/theorems/7fbd0b40-ee45-4674-82c9-2793c9ddda32
-- title:
--   Pure states, orthonormal pairs and support on a subspace
-- statement:
--   Vectors on a register with basis $\iota$ are functions $\psi:\iota\to\mathbb C$, with the standard inner product $\langle v,w\rangle=\sum_i\overline{v_i}w_i$.
--
--   1. $|\psi\rangle\langle\psi|$ is the matrix with entries $\psi_i\overline{\psi_j}$; $|\psi_0\rangle\otimes|\psi_1\rangle$ is the vector $(i_0,i_1)\mapsto\psi_0(i_0)\psi_1(i_1)$.
--   2. $\psi$ is a **unit vector** if $\langle\psi,\psi\rangle=1$; a pair $e_0,e_1$ is **orthonormal** if $\langle e_a,e_b\rangle=\delta_{ab}$.
--   3. For a subspace $S\le\mathbb C^\iota$, a matrix $\sigma$ is **supported on $S$** if $\sigma v=0$ for every $v$ orthogonal to $S$.
--
--   In the paper, $S_b$ is the accepting subspace of the projective verifier $\mathrm{Ver}_b$ and an input is valid if it is supported on $S_b$; the honest party's outputs must be supported on the appropriate accepting subspace.
--
--   **Formalization Note** For a Hermitian (in particular positive semidefinite) $\sigma$, support on $S$ is the same as $\operatorname{range}\sigma\subseteq S$, i.e. $\Pi_S\sigma\Pi_S=\sigma$. The zero matrix, a probability-zero branch, is supported on every subspace.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §4.1, p.18; §3.1, p.13

import Mathlib

namespace QFairEx

open Matrix

/-- **The density operator `|ψ⟩⟨ψ|` of a vector**, `(|ψ⟩⟨ψ|)_{i j} = ψ_i · conj(ψ_j)`.
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §3.1, p.13 ("We write |ϕ⟩⟨ϕ|"). -/
def pureDensity {ι : Type} (ψ : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec ψ (star ψ)

/-- **Product vector** `|ψ₀⟩ ⊗ |ψ₁⟩` on `ι₀ × ι₁`. -/
def prodVec {ι0 ι1 : Type} (ψ0 : ι0 → ℂ) (ψ1 : ι1 → ℂ) : ι0 × ι1 → ℂ := fun i => ψ0 i.1 * ψ1 i.2

/-- **Unit vector**: `⟨ψ, ψ⟩ = ∑_i conj(ψ_i) ψ_i = 1` (a normalized pure state). -/
def IsUnitVec {ι : Type} [Fintype ι] (ψ : ι → ℂ) : Prop := star ψ ⬝ᵥ ψ = 1

/-- **Orthonormal pair** `e 0, e 1`: `⟨e a, e b⟩ = δ_{ab}` for the standard inner product.
Used for the states `|e_{p,0}⟩, |e_{p,1}⟩` of §4.2.2, p.22. -/
def IsOrthonormalPair {ι : Type} [Fintype ι] (e : Fin 2 → ι → ℂ) : Prop :=
  ∀ a b : Fin 2, star (e a) ⬝ᵥ e b = if a = b then 1 else 0

/-- **A (subnormalized) state supported on a subspace.**
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.1, p.18: "S_b denotes the accepting subspace of Ver_b, and an
input to Ver_b is valid if it is supported on S_b."

`SupportedOn S σ` says that `σ v = 0` for every vector `v` orthogonal (for the standard inner
product `⟨v, s⟩ = ∑ conj(v_i) s_i`) to every `s ∈ S`.

**Formalization Note.** For a Hermitian (in particular positive semidefinite) `σ` this is the
same as `range σ ⊆ S`, i.e. `Π_S σ Π_S = σ` for the orthogonal projection `Π_S`. The zero matrix
is supported on every subspace, as a probability-zero branch should be. -/
def SupportedOn {ι : Type} [Fintype ι] (S : Submodule ℂ (ι → ℂ)) (σ : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, (∀ s ∈ S, star v ⬝ᵥ s = 0) → σ *ᵥ v = 0

end QFairEx


