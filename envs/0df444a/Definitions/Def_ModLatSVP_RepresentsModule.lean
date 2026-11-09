-- Prove2me | Definitions.Def_ModLatSVP_RepresentsModule
-- name    : ModLatSVP_RepresentsModule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:45.328213+00:00
-- url     : https://prove2.me/theorems/dcf29b03-ec92-4fc0-8fb2-0e6bdbf73aa5
-- title:
--   Integral bases, multiplication tables, involution matrices, and the module input
-- statement:
--   Let $K$ be a number field with involution $\star$, and $E$ a subfield. A family $\beta_1,\dots,\beta_e\in K$ is an **integral basis** of $E$ if it is a $\mathbb Z$-basis of $\mathcal O_E=E\cap\mathcal O_K$. Its **multiplication table** is the array $c_{abk}\in\mathbb Z$ with $\beta_a\beta_b=\sum_kc_{abk}\beta_k$, and the **involution matrix** is $S\in\mathbb Z^{e\times e}$ with $\beta_a^\star=\sum_kS_{ka}\beta_k$.
--
--   The **field data** of $K$ are an integral basis $\omega_1,\dots,\omega_d$ of $\mathcal O_K$ given by its multiplication table and its involution matrix. The **module input** consists of the field data, a positive definite rational Gram matrix $G\in\mathbb Q^{N\times N}$ of the lattice $\mathbb Z^N$, and integer matrices $A_1,\dots,A_d$, where $A_i=A(\omega_i)$ describes multiplication by $\omega_i$; the input represents a module when these matrices extend to an action of $K$ on $\mathbb Q^N$ that is compatible with $G$:
--
--   $$A(\alpha)^{T}G=G\,A(\alpha^\star).$$
--
--   This is the input model of the paper for module-SVP and module-CVP.
--
--   **Formalization Note** The "supplied integral basis" is represented by its multiplication table and involution matrix, the data an algorithm computes with; the field $K$ itself is not part of the input. Matrices act on coefficient columns.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.2, p.12 (PDF p.12); Lemma 3.6, p.21; proof of Lemma 3.6, p.22; proof of Corollary 3.7, p.23

import Mathlib
import Definitions.Def_ModLatSVP_IsCompatible

open NumberField

namespace ModLatSVP

/-- `β₁, …, β_e` is an integral basis of the subfield `E`: a `ℤ`-basis of `𝒪_E = E ∩ 𝒪_K` (proof of
Lemma 3.6, p.22: "For E ⊆ F, we have 𝒪_E = E ∩ 𝒪_F"). Kim, Lee, Son, *Exact SVP and CVP in Structured
Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…), §2.2, p.12. -/
def IsIntBasisOf (K : Type*) [Field K] [CharZero K] (E : IntermediateField ℚ K) {e : ℕ}
    (β : Fin e → K) : Prop :=
  (∀ a, β a ∈ E ∧ IsIntegral ℤ (β a)) ∧ LinearIndependent ℤ β ∧
  ∀ x ∈ E, IsIntegral ℤ x → ∃ z : Fin e → ℤ, x = ∑ a, (z a : K) * β a

/-- `c` is the multiplication table of `β`: `β_a β_b = Σ_k c_{abk} β_k`. -/
def HasTable {K : Type*} [Field K] {e : ℕ} (β : Fin e → K) (c : Fin e → Fin e → Fin e → ℤ) : Prop :=
  ∀ a b, β a * β b = ∑ k, (c a b k : K) * β k

/-- `S` is the matrix of the involution `⋆ = τ` on `β` (column convention): `β_a⋆ = Σ_k S_{ka} β_k`. -/
def HasInvolution {K : Type*} [Field K] [CharZero K] (τ : K ≃ₐ[ℚ] K) {e : ℕ} (β : Fin e → K)
    (S : Matrix (Fin e) (Fin e) ℤ) : Prop :=
  ∀ a, τ (β a) = ∑ k, (S k a : K) * β k

/-- The field data of the module input (§2.2, p.12, and proof of Corollary 3.7, p.23: "The module input
already includes the integral arithmetic and involution of K"): `ω` is an integral basis of `𝒪_K`, `c`
its multiplication table and `S` the matrix of `⋆` on it.

**Formalization Note.** The "supplied integral basis" is represented by its multiplication table and the
involution matrix, the data an algorithm computes with. `d` equals `[K : ℚ]` because `ω` is a `ℤ`-basis
of `𝒪_K`. -/
def RepresentsField (K : Type*) [Field K] [CharZero K] (τ : K ≃ₐ[ℚ] K) {d : ℕ} (ω : Fin d → K)
    (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  IsIntBasisOf K ⊤ ω ∧ HasTable ω c ∧ HasInvolution τ ω S

/-- The module input of §2.2, p.12: the lattice `ℤ^N` with positive definite rational Gram matrix `G`
and integer matrices `A_i = A(ω_i)` of multiplication by the integral basis `ω`, satisfying
`A(α)ᵀ G = G A(α⋆)`. `RepresentsModule K τ ω G A` says that the `A_i` extend to an action
`φ : K →+* Matrix (Fin N) (Fin N) ℚ` on `ℚ^N = M ⊗ ℚ` (column convention) that is compatible with `G`
(`IsCompatible`).

**Formalization Note.** Such `φ` is unique and maps `𝒪_K` to integer matrices because `ω` spans `𝒪_K`;
compatibility on all of `K` is equivalent to the paper's condition on the basis by `ℚ`-linearity. -/
def RepresentsModule (K : Type*) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) {d N : ℕ}
    (ω : Fin d → K) (G : Matrix (Fin N) (Fin N) ℚ) (A : Fin d → Matrix (Fin N) (Fin N) ℤ) : Prop :=
  ∃ φ : K →+* Matrix (Fin N) (Fin N) ℚ,
    (∀ i, φ (ω i) = (A i).map (fun z : ℤ => (z : ℚ))) ∧
    IsCompatible K τ (G.map (fun q : ℚ => (q : ℝ))) φ

end ModLatSVP


