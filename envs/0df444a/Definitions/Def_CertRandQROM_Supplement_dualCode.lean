-- Prove2me | Definitions.Def_CertRandQROM_Supplement_dualCode
-- name    : CertRandQROM_Supplement_dualCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:41:09.41734+00:00
-- url     : https://prove2.me/theorems/d0773639-25f7-4c68-9a7d-21c1d5b4d1e4
-- title:
--   Dual code $C^\perp$ of a folded code (unfolded dot product)
-- statement:
--   Let $\Sigma=\mathbb F_q^m$ and let $C\subseteq\Sigma^n$ be a code. Words of $\Sigma^n$ are identified with vectors of $\mathbb F_q^{nm}$ by concatenating the $n$ blocks, and the dot product of two words is
--
--   $$
--   x\cdot z=\sum_{i\in[n]}\sum_{j\in[m]}x_{i,j}\,z_{i,j}\in\mathbb F_q .
--   $$
--
--   The **dual code** is
--
--   $$
--   C^\perp=\{z\in\Sigma^n:\ x\cdot z=0\ \ \forall x\in C\}.
--   $$
--
--   The honest prover of Construction 6.2 decodes in the dual of the folded Reed–Solomon code $C_\lambda$; the quantum Fourier transform maps the uniform superposition over $C$ to the one over $C^\perp$.
--
--   **Formalization Note** Words are functions `Fin n → Fin m → K`; `unfoldDot` is the dot product. The definition applies to any finite field and any subset $C$; the paper uses it for the linear code $C_\lambda$.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §5.1, Folded Linear Codes and Dual Codes, p.22 (PDF p.24)

import Mathlib

set_option autoImplicit false

namespace CertRandQROM.Supplement

/-- The **unfolded dot product** of two folded words `x, z ∈ Σ^n`, `Σ = F_q^m`
(Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, *Unconditional Certified Randomness without
Structure*, arXiv:2608.31112 (sha256 b75095a2…), §5.1 "Folded Linear Codes" and "Dual Codes",
p.22): the code is embedded into `F_q^{n·m}` "in the canonical way", so
`x · z = Σ_{i ∈ [n]} Σ_{j ∈ [m]} x_{i,j} z_{i,j}`. -/
def unfoldDot {K : Type} [Field K] {n m : ℕ} (x z : Fin n → Fin m → K) : K :=
  ∑ i, ∑ j, x i j * z i j

open Classical in
/-- **The dual code** `C⊥ = {z ∈ Σ^n : x · z = 0 ∀ x ∈ C}` of a folded code `C ⊆ Σ^n`,
`Σ = F_q^m` (§5.1 "Dual Codes", p.22 of arXiv:2608.31112, sha256 b75095a2…), with `·` the
unfolded `F_q` dot product `unfoldDot`.

**Formalization Note** Words are `Fin n → Fin m → K` (block `i`, coordinate `j` of the block);
`Alph F λ = Fin (mPar λ) → F λ` of the base mission is this alphabet. The definition is stated for
any finite field `K` and any code `C`; the paper applies it to the linear code `C_λ`. -/
noncomputable def dualCode {K : Type} [Field K] [Fintype K] [DecidableEq K] {n m : ℕ}
    (C : Finset (Fin n → Fin m → K)) : Finset (Fin n → Fin m → K) :=
  Finset.univ.filter fun z => ∀ x ∈ C, unfoldDot x z = 0

end CertRandQROM.Supplement


