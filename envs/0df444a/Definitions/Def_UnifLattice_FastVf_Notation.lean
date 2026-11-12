-- Prove2me | Definitions.Def_UnifLattice_FastVf_Notation
-- name    : UnifLattice_FastVf_Notation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:18:01.010081+00:00
-- url     : https://prove2.me/theorems/8bed9141-bcf1-440b-9d1b-a39301821686
-- title:
--   Notation of §2.1 and §3.1: bit strings associated with indices, vector Kronecker products, the norm ∥A∥ and J_L of Lemma 2.1
-- statement:
--   For $L=2^\ell$, an index $i\in[L]=\{1,\dots,L\}$ is identified with the **bit string associated with $i$**, $(i_1,\dots,i_\ell)\in\{0,1\}^\ell$, the binary representation of $i-1$ with $i_1$ the most significant bit (§3.1, p. 21). For $(i,j,k)\in[L]^3$ the associated bit string is
--   $$z=(z_1,\dots,z_{3\ell})=(i_1,\dots,i_\ell,\,j_1,\dots,j_\ell,\,k_1,\dots,k_\ell)\in\{0,1\}^{3\ell}\quad\text{(p. 23)}.$$
--   For a matrix $A\in\mathbb Z^{n\times m}$, $\|A\|=\max_{i\in[m]}\|a_i\|_\infty$ over its columns $a_i$, i.e. the largest absolute value of an entry (p. 16). $u\otimes v$ is the Kronecker product, and $\mathrm{vec}(A)$ stacks the columns of $A$. The **compactification matrix** of Lemma 2.1 (p. 17) is
--   $$J_L=I_L\otimes \mathrm{vec}(I_m)\in\{0,1\}^{Lm^2\times L}.$$
--
--   These objects fix the index conventions used by every other item of the mission.
--
--   **Formalization Note.** Indices are 0-based: `i : Fin (2^ℓ)` stands for the paper's $i-1$, and position `t : Fin ℓ` for the paper's position $t+1$; `assocBit ℓ i t` is the paper's $i_{t+1}$ and `assocString ℓ i j k p` is $z_{p+1}$. Bits are `Fin 2`. `splitMSB ℓ` splits a 0-based index of $[2L]$ into its most significant bit and the rest, $i\mapsto(\lfloor i/L\rfloor, i \bmod L)$. Vectors are functions on index types and `kron u v` is indexed by pairs (the lexicographic order of pairs is the order of the Kronecker product). `entryNorm A` is a natural number, `0` for a matrix without entries. `J ι m` is $J_L$ for $L=|\iota|$, with rows $\iota\times(\text{column},\text{row})$, as Mathlib's `Matrix.vec` indexes $\mathrm{vec}(I_m)$.
-- source:
--   Wee, Wichs, Wu, SNARGs and ABE for Uniform Computations via Lattice Encodings, STOC 2027 submission (manuscript sha256 fd77662e…), p. 16 (§2.1), p. 17 (Lemma 2.1), pp. 21 and 23 (§3.1 Notation)

import Mathlib

open Matrix
open scoped Kronecker

/-!
# Notation of §2, §2.1 and §3.1: bit strings of indices, vector Kronecker products, the entry
norm and the compactification matrix `J_L` (Lemma 2.1)

Wee, Wichs, Wu, *SNARGs and ABE for Uniform Computations via Lattice Encodings*, STOC 2027
submission (manuscript sha256 fd77662e…), p. 16 (§2, §2.1), p. 17 (Lemma 2.1), p. 21 and p. 23
(§3.1 "Notation", the bit string associated with `(i, j, k)`).

Conventions. An index `i ∈ [L]` (`L = 2^ℓ`) of the paper is represented by the 0-based
`i - 1 : Fin (2 ^ ℓ)`. The paper's bit positions `1, …, ℓ` and `1, …, 3ℓ` are `0, …, ℓ - 1` and
`0, …, 3ℓ - 1`. A bit is an element of `Fin 2 = {0, 1}`.
-/

namespace UnifLattice.FastVf

/-- The bit string `(i₁, …, i_ℓ) ∈ {0,1}^ℓ` associated with an index (§3.1, p. 21): the binary
representation of `i - 1`, most significant bit first. Here `i` is the 0-based index `i - 1`, and
`assocBit ℓ i t` is the paper's `i_{t+1}`, i.e. the bit of weight `2^(ℓ - 1 - t)` of `i - 1`. -/
def assocBit (ℓ : ℕ) (i : Fin (2 ^ ℓ)) (t : Fin ℓ) : Fin 2 :=
  ⟨(i.val / 2 ^ (ℓ - 1 - t.val)) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The bit string `z = (i₁, …, i_ℓ, j₁, …, j_ℓ, k₁, …, k_ℓ) ∈ {0,1}^{3ℓ}` associated with
`(i, j, k) ∈ [L]³` (p. 23). Position `p` (0-based) is the paper's `z_{p+1}`. -/
def assocString (ℓ : ℕ) (i j k : Fin (2 ^ ℓ)) (p : Fin (3 * ℓ)) : Fin 2 :=
  if h₁ : p.val < ℓ then assocBit ℓ i ⟨p.val, h₁⟩
  else if h₂ : p.val < 2 * ℓ then assocBit ℓ j ⟨p.val - ℓ, by omega⟩
  else assocBit ℓ k ⟨p.val - 2 * ℓ, by omega⟩

/-- Split of a 0-based index of `[2L]` into its most significant bit and the remaining index of
`[L]`: `i ↦ (i / L, i mod L)` with `L = 2^ℓ`. The vector `x ∈ {0,1}^{2L}` parsed as
`(x₀; x₁)` (top half `x₀`) has `x₀ = x ∘ (splitMSB ℓ).symm (0, ·)`, and the column blocks of a
matrix `[A₀ | A₁]` with `L` blocks each are indexed the same way. -/
def splitMSB (ℓ : ℕ) : Fin (2 ^ (ℓ + 1)) ≃ Fin 2 × Fin (2 ^ ℓ) :=
  (finProdFinEquiv.trans (finCongr (by ring))).symm

/-- Kronecker product `u ⊗ v` of two column vectors (§2.1), indexed by pairs: `(u ⊗ v)_(a,b) =
u_a v_b`. With the lexicographic order on pairs this is the usual Kronecker product. -/
def kron {ι κ : Type} (u : ι → ℤ) (v : κ → ℤ) : ι × κ → ℤ :=
  fun p => u p.1 * v p.2

/-- The norm `∥A∥ = max_i ∥a_i∥` of an integer matrix (§2.1, p. 16): the maximum over the columns
`a_i` of their `ℓ∞` norm, i.e. the largest absolute value of an entry. It is `0` for a matrix with
no entries. -/
def entryNorm {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℤ) : ℕ :=
  Finset.univ.sup fun p : ι × κ => (A p.1 p.2).natAbs

/-- The compactification matrix `J_L = I_L ⊗ vec(I_m) ∈ {0,1}^{Lm² × L}` of Lemma 2.1 (p. 17), for
`L` the cardinality of the index type `ι`. `Matrix.vec` stacks columns, so `vec(I_m)` is indexed by
(column, row) pairs; the column vector `vec(I_m)` has the single column `Unit`. -/
def J (ι : Type) [DecidableEq ι] (m : ℕ) : Matrix (ι × (Fin m × Fin m)) (ι × Unit) ℤ :=
  (1 : Matrix ι ι ℤ) ⊗ₖ replicateCol Unit (vec (1 : Matrix (Fin m) (Fin m) ℤ))

end UnifLattice.FastVf


