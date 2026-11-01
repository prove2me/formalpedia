-- Prove2me | Definitions.Def_SymTensorNet_IrrepCatalogue
-- name    : SymTensorNet_IrrepCatalogue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:45.271986+00:00
-- url     : https://prove2.me/theorems/e6419fe7-b66e-4eff-b4dd-aa7a53785b33
-- title:
--   Irreducible unitary matrix representations, their equivalence, and a catalogue of irreps labelled by charges
-- statement:
--   Let $G$ be a group. A **unitary matrix representation** of dimension $n$ is a group homomorphism $\rho: G\to U(n)$, $g\mapsto\rho_g$, into the $n\times n$ unitary matrices.
--
--   1. $\rho$ is **irreducible** when $n>0$ and the only subspaces of $\mathbb C^n$ invariant under every $\rho_g$ are $0$ and $\mathbb C^n$.
--   2. Two representations $\rho$ (dimension $m$) and $\sigma$ (dimension $n$) are **equivalent** when there is an invertible matrix $X$ ($m\times n$, with a two-sided inverse $Y$) such that $\rho_g X = X\sigma_g$ for all $g$.
--   3. A **catalogue of irreps** is a set $A$ of **charges** $a$ (with decidable equality), and for each charge an irreducible unitary representation
--   $$U^a: G\to U(\dim a),$$
--   such that distinct charges label inequivalent representations. The space of the irrep $a$ is $\mathbb V^a=\mathbb C^{\dim a}$ with orthonormal basis $|a,m_a\rangle$, $m_a=1,\dots,\dim a$.
--   4. A catalogue $C$ **covers** a matrix representation $U$ on $\mathbb C^n$ when every irreducible unitary representation $\sigma$ that occurs in $U$ (that is, admits a nonzero matrix $X$ with $U_gX=X\sigma_g$ for all $g$) is equivalent to $U^a$ for some charge $a$.
--
--   These are the irreps "labeled with charge $a$" of the paper, and "covers" says that the decomposition of a representation into irreps uses only labelled irreps.
--
--   **Formalization Note** $G$ is an arbitrary group, with no topology; the compact groups of the paper, with their continuous irreps, are an instance. The set of charges may be infinite (as for $SU(2)$).
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (4) and the paragraph after it, p.2; Eq. (9), p.2

import Mathlib

namespace SymTensorNet

universe u v

open Matrix

/-- A unitary matrix representation `ρ : G → U(n)` is **irreducible** when `n > 0` and the only
subspaces of `ℂⁿ` invariant under every `ρ g` are `0` and `ℂⁿ`.

Singh, Pfeifer & Vidal, *Tensor network decompositions in the presence of a global symmetry*,
arXiv:0907.2994v2, p.2, Eq. (4): "irreducible representations (irreps) of G".

**Formalization Note** The group `G` is a bare `Group`: no topology and no continuity is
required (the paper's compact group is an instance). -/
def IsIrrep {G : Type*} [Group G] {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) : Prop :=
  0 < n ∧
    ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ (g : G), ∀ v ∈ W, (ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

/-- Two matrix representations are **equivalent** when an invertible matrix intertwines them:
`ρ g * X = X * σ g` for all `g`, with `X * Y = 1` and `Y * X = 1`.

arXiv:0907.2994v2, p.2, Eq. (4) ("the irrep labeled with charge a"); distinct charges label
inequivalent irreps. -/
def RepEquiv {G : Type*} [Group G] {m n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin m) ℂ)
    (σ : G →* Matrix.unitaryGroup (Fin n) ℂ) : Prop :=
  ∃ (X : Matrix (Fin m) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ),
    X * Y = 1 ∧ Y * X = 1 ∧
      ∀ g : G, (ρ g : Matrix (Fin m) (Fin m) ℂ) * X = X * (σ g : Matrix (Fin n) (Fin n) ℂ)

/-- A **catalogue of irreps** of `G`: a type of charges `a`, and for each charge an irreducible
unitary matrix representation `Uᵃ : G → U(dim a)`, with distinct charges labelling inequivalent
representations.

arXiv:0907.2994v2, p.2, Eq. (4): "𝕍ᵃ denotes the irrep labeled with charge a".

**Formalization Note** Charges form an arbitrary type (possibly infinite, as for SU(2)), with
decidable equality. Irreps are given as matrices in a fixed orthonormal basis `|a, m_a⟩`,
`m_a ∈ Fin (dim a)`. -/
structure IrrepCatalogue (G : Type u) [Group G] : Type (max u (v + 1)) where
  /-- The charges (irrep labels). -/
  Charge : Type v
  /-- Decidable equality of charges. -/
  [decEq : DecidableEq Charge]
  /-- The dimension of the irrep with charge `a`. -/
  dim : Charge → ℕ
  /-- The unitary matrix representation `Uᵃ`. -/
  rep : (a : Charge) → G →* Matrix.unitaryGroup (Fin (dim a)) ℂ
  /-- Each `Uᵃ` is irreducible. -/
  irrep : ∀ a, IsIrrep (rep a)
  /-- Distinct charges label inequivalent irreps. -/
  inequiv : ∀ a b, a ≠ b → ¬ RepEquiv (rep a) (rep b)

attribute [instance] IrrepCatalogue.decEq

/-- The catalogue `C` **covers** the matrix representation `U : G → M_n(ℂ)` when every
irreducible unitary representation `σ` occurring in `U` (that is, admitting a nonzero
intertwiner `X` with `U g * X = X * σ g`) is equivalent to a member of the catalogue.

arXiv:0907.2994v2, p.2, Eq. (4) ("decomposes as the direct sum of irreducible
representations") and Eq. (9) ("can be decomposed as the direct sum of irreps"). -/
def Covers {G : Type*} [Group G] (C : IrrepCatalogue G) {n : Type*} [Fintype n] [DecidableEq n]
    (U : G → Matrix n n ℂ) : Prop :=
  ∀ (k : ℕ) (σ : G →* Matrix.unitaryGroup (Fin k) ℂ), IsIrrep σ →
    (∃ X : Matrix n (Fin k) ℂ, X ≠ 0 ∧ ∀ g : G, U g * X = X * (σ g : Matrix (Fin k) (Fin k) ℂ)) →
      ∃ a : C.Charge, RepEquiv σ (C.rep a)

end SymTensorNet


