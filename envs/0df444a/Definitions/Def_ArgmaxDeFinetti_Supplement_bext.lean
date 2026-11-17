-- Prove2me | Definitions.Def_ArgmaxDeFinetti_Supplement_bext
-- name    : ArgmaxDeFinetti_Supplement_bext
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:40:46.274857+00:00
-- url     : https://prove2.me/theorems/a7340520-9f78-4cad-ae3c-19f0bce48c8f
-- title:
--   Bipartite separable states $\mathrm{SEP}(d_A,d_B)$ and two-sided Bose-symmetric extendible states $\mathrm{BEXT}_{n,m}(d_A,d_B)$
-- statement:
--   The **bipartite separable states** on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ are
--
--   $$
--   \mathrm{SEP}(d_A,d_B)=\mathrm{conv}\{|u\rangle\langle u|\otimes|v\rangle\langle v|:\ u\in\mathbb C^{d_A},\ v\in\mathbb C^{d_B},\ \|u\|=\|v\|=1\}.
--   $$
--
--   For $n,m\ge1$, the **two-sided Bose-symmetric extendible states** are the marginals
--
--   $$
--   \mathrm{BEXT}_{n,m}(d_A,d_B)=\{\tilde\rho_{A_1B_1}:\ \tilde\rho\in D(\mathrm{Sym}^n(\mathbb C^{d_A})\otimes\mathrm{Sym}^m(\mathbb C^{d_B}))\},
--   $$
--
--   where $\tilde\rho_{A_1B_1}$ is obtained by tracing out $A_2,\dots,A_n,B_2,\dots,B_m$ from a state of $(\mathbb C^{d_A})^{\otimes n}\otimes(\mathbb C^{d_B})^{\otimes m}$ supported on the product of the two symmetric subspaces.
--
--   They are the outer relaxation of $\mathrm{SEP}(d_A,d_B)$ used for disentanglers, Best Separable State and separability testing.
--
--   **Formalization Note** A state on the subspace is a density operator $\tilde\rho$ on the whole space with $(U_\pi\otimes I)\tilde\rho=\tilde\rho$ and $(I\otimes U_\tau)\tilde\rho=\tilde\rho$ for all $\pi\in S_n$, $\tau\in S_m$ (range in $\mathrm{Sym}^n\otimes\mathrm{Sym}^m$). This is symmetric support in each block, stronger than permutation invariance. Operators on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$ are matrices indexed by pairs, $\otimes$ is the Kronecker product, and $\mathrm{conv}$ the real convex hull.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Two-sided extendible states", eq. (2.3), p.19

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_ArgmaxDeFinetti_vnorm
import Definitions.Def_ArgmaxDeFinetti_Supplement_marginal

open Matrix
open scoped Kronecker

namespace ArgmaxDeFinetti

namespace Supplement

/-- The bipartite separable states
`SEP(dA, dB) = conv{|u⟩⟨u| ⊗ |v⟩⟨v| : u ∈ ℂ^{dA}, v ∈ ℂ^{dB}, ∥u∥ = ∥v∥ = 1}`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Two-sided extendible
states", p.19.

**Formalization Note** Operators on `ℂ^{dA} ⊗ ℂ^{dB}` are matrices indexed by `Fin dA × Fin dB`, `⊗` is the
Kronecker product `⊗ₖ`, `conv` is `convexHull ℝ` and `∥·∥` the Euclidean norm `vnorm`. -/
def sepAB (dA dB : ℕ) : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  convexHull ℝ {σ | ∃ (u : Fin dA → ℂ) (v : Fin dB → ℂ), vnorm u = 1 ∧ vnorm v = 1 ∧
    σ = Matrix.vecMulVec u (star u) ⊗ₖ Matrix.vecMulVec v (star v)}

/-- `ρ̃ ∈ D(Sym^n(ℂ^{dA}) ⊗ Sym^m(ℂ^{dB}))`: a density operator on `(ℂ^{dA})^{⊗n} ⊗ (ℂ^{dB})^{⊗m}` whose range lies
in `Sym^n(ℂ^{dA}) ⊗ Sym^m(ℂ^{dB})`, i.e. `(U_π ⊗ I) ρ̃ = ρ̃` and `(I ⊗ U_τ) ρ̃ = ρ̃` for all `π ∈ S_n`, `τ ∈ S_m`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1, eq. (2.3), p.19.

**Formalization Note** A density operator on the subspace is identified with its extension by zero, exactly as the
base mission's `IsBosonic`; range in `Sym^n ⊗ Sym^m` is invariance of every column under both block permutation
groups. This is symmetric support in each block, not mere permutation invariance (which defines `EXT_{n,m}`). -/
def IsBEXTState {n m dA dB : ℕ}
    (ρ : Matrix ((Fin n → Fin dA) × (Fin m → Fin dB)) ((Fin n → Fin dA) × (Fin m → Fin dB)) ℂ) : Prop :=
  WildeQIT.IsDensityOperator ρ ∧
    (∀ π : Equiv.Perm (Fin n),
      (OptimalSpectrum.Entangled.permOp (ι := Fin dA) π ⊗ₖ (1 : Matrix (Fin m → Fin dB) (Fin m → Fin dB) ℂ)) * ρ = ρ) ∧
    (∀ τ : Equiv.Perm (Fin m),
      ((1 : Matrix (Fin n → Fin dA) (Fin n → Fin dA) ℂ) ⊗ₖ OptimalSpectrum.Entangled.permOp (ι := Fin dB) τ) * ρ = ρ)

/-- The `A₁B₁` marginal `ρ̃_{A₁B₁} = Tr_{A₂…A_n B₂…B_m} ρ̃` of an operator on `(ℂ^{dA})^{⊗n} ⊗ (ℂ^{dB})^{⊗m}`: the
first site of each block is kept, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1, eq. (2.3), p.19.

**Formalization Note** Used with `n, m ≥ 1`. The first site of the `A`-block has index `0`; the traced sites are
`1, …, n − 1` (resp. `m − 1`), joined by `joinIdx`. -/
def marginalA1B1 {n m dA dB : ℕ}
    (ρ : Matrix ((Fin n → Fin dA) × (Fin m → Fin dB)) ((Fin n → Fin dA) × (Fin m → Fin dB)) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  fun x y => ∑ c : Fin (n - 1) → Fin dA, ∑ e : Fin (m - 1) → Fin dB,
    ρ (joinIdx ![x.1] c, joinIdx ![x.2] e) (joinIdx ![y.1] c, joinIdx ![y.2] e)

/-- The two-sided Bose-symmetric extendible states
`BEXT_{n,m}(dA, dB) = {ρ̃_{A₁B₁} : ρ̃ ∈ D(Sym^n(ℂ^{dA}) ⊗ Sym^m(ℂ^{dB}))}`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1, eq. (2.3), p.19.

**Formalization Note** Used with `n, m ≥ 1` (the paper's "For n, m ≥ 1"). -/
def bext (n m dA dB : ℕ) : Set (Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :=
  {τ | ∃ ρ : Matrix ((Fin n → Fin dA) × (Fin m → Fin dB)) ((Fin n → Fin dA) × (Fin m → Fin dB)) ℂ,
    IsBEXTState ρ ∧ τ = marginalA1B1 ρ}

end Supplement

end ArgmaxDeFinetti


