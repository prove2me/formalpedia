-- Prove2me | Definitions.Def_ModLatSVP_RepresentsChain
-- name    : ModLatSVP_RepresentsChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:32.467309+00:00
-- url     : https://prove2.me/theorems/3c9860a8-f3e9-4ef9-a61c-1951542f94e4
-- title:
--   Chain data — levels of a subfield chain with integral bases, tables, involutions, inclusions
-- statement:
--   Let $K$ have field data with integral basis $\omega_1,\dots,\omega_d$. A **level** of chain data consists of a degree $e$, a multiplication table, an involution matrix, and an inclusion matrix $I\in\mathbb Z^{e\times d}$, describing the family $\beta_a=\sum_bI_{ab}\omega_b$. A list of levels $K_1,\dots,K_h$ **represents a chain** with relative degrees at most $s_0$ and terminal degree at most $d_0$ if there is a subfield chain $K=K_0\supsetneq K_1\supsetneq\cdots\supsetneq K_h$ with these bounds such that, for each $j\ge1$, the $j$-th level's family is an integral basis of $K_j$ with the given multiplication table, and the given involution matrix is that of the restriction of $\star$ to $K_j$.
--
--   This is the chain data supplied to the algorithms of Theorems 3.4 and 3.5, and produced by Lemma 3.6(i).
--
--   **Formalization Note** Each subfield is represented in the coordinates of $K$'s integral basis ("inclusion into $K$"); the inclusions between consecutive levels follow by exact linear algebra. Level $K_0=K$ is described by the field data of the module input.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 3.4, p.20 (PDF p.20); §3.1, p.17; Lemma 3.6, p.21; proof of Lemma 3.6, p.22

import Mathlib
import Definitions.Def_ModLatSVP_IsChain
import Definitions.Def_ModLatSVP_RepresentsModule

namespace ModLatSVP

/-- The data of one subfield `K_j` of a chain in `K` (Theorem 3.4, p.20: "integral bases, multiplication
tables, inclusions, and involutions ⋆ compatible with the inclusions"; Lemma 3.6, p.21: "returned with an
integral basis, multiplication table, involution, and inclusion into K"). Kim, Lee, Son, *Exact SVP and
CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission
(manuscript sha256 e7151fad…).

`e` is the degree, `c` the multiplication table and `S` the involution matrix of an integral basis
`β_1, …, β_e` of `𝒪_{K_j}`, and `incl` expresses that basis in the integral basis `ω` of `K`:
`β_a = Σ_b incl_{ab} ω_b` (the paper's "Represent each subfield in the original coordinates of K",
p.22). -/
structure FieldLevel (d : ℕ) where
  e : ℕ
  c : Fin e → Fin e → Fin e → ℤ
  S : Matrix (Fin e) (Fin e) ℤ
  incl : Matrix (Fin e) (Fin d) ℤ

/-- The basis `β_a = Σ_b incl_{ab} ω_b` that a level describes. -/
def levelBasis {K : Type*} [Field K] {d : ℕ} (ω : Fin d → K) (L : FieldLevel d) : Fin L.e → K :=
  fun a => ∑ b, (L.incl a b : K) * ω b

/-- The levels `Ls = [K_1, …, K_h]` describe the fields `F 1, …, F h`: for each `j < h`, the basis of
level `j` is an integral basis of `F (j+1)`, with the given multiplication table, and the given matrix
of the restriction of `⋆`. -/
def RepresentsChainAt (K : Type*) [Field K] [CharZero K] (τ : K ≃ₐ[ℚ] K) {d : ℕ} (ω : Fin d → K)
    (F : ℕ → IntermediateField ℚ K) (Ls : List (FieldLevel d)) : Prop :=
  ∀ (j : ℕ) (hj : j < Ls.length),
    IsIntBasisOf K (F (j + 1)) (levelBasis ω Ls[j]) ∧ HasTable (levelBasis ω Ls[j]) Ls[j].c ∧
      HasInvolution τ (levelBasis ω Ls[j]) Ls[j].S

/-- Supplied chain data (Theorem 3.4, p.20): a chain `K = K₀ ⊋ K₁ ⊋ ⋯ ⊋ K_h` with
`[K_j : K_{j+1}] ≤ s₀` and `[K_h : ℚ] ≤ d₀` (`IsChain`), described level by level by `Ls` (`h` is the
length of `Ls`; level `K₀ = K` is described by the module input itself). -/
def RepresentsChain (K : Type*) [Field K] [CharZero K] (τ : K ≃ₐ[ℚ] K) {d : ℕ} (ω : Fin d → K)
    (s₀ d₀ : ℕ) (Ls : List (FieldLevel d)) : Prop :=
  ∃ F : ℕ → IntermediateField ℚ K, IsChain K s₀ d₀ F Ls.length ∧ RepresentsChainAt K τ ω F Ls

end ModLatSVP


