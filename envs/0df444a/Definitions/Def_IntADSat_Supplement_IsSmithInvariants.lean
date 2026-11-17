-- Prove2me | Definitions.Def_IntADSat_Supplement_IsSmithInvariants
-- name    : IntADSat_Supplement_IsSmithInvariants
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:41:36.432614+00:00
-- url     : https://prove2.me/theorems/5aa24f81-877c-48ee-a75a-9917af081574
-- title:
--   Smith invariants of a sublattice of $\mathbb Z^n$
-- statement:
--   Let $\Lambda\subseteq\mathbb Z^n$ be a subgroup. A list $s=(s_1,\dots,s_r)$ of natural numbers is the list of **Smith invariants** of $\Lambda$ if
--
--   1. every $s_i$ is positive and $s_1\mid s_2\mid\cdots\mid s_r$, and
--   2. there is a basis $b_1,\dots,b_n$ of $\mathbb Z^n$ with $r\le n$ and
--   $$\Lambda=\mathbb Z s_1b_1\oplus\cdots\oplus\mathbb Z s_rb_r .$$
--
--   Then $r=\operatorname{rank}\Lambda$ and $\mathbb Z^n/\Lambda\cong\mathbb Z^{n-r}\oplus\bigoplus_i\mathbb Z/s_i\mathbb Z$; the list (with its leading ones) is the nonzero diagonal of the Smith normal form of any generating matrix of $\Lambda$, and is unique. Theorem A.6 asserts that these invariants of the word lattice $\Lambda_G$ are computable in polynomial time.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem A.6, p.13 (PDF 14); proof of Proposition A.2, p.12 (PDF 13)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- `s = (s_1, …, s_r)` are the **Smith invariants** of a sublattice `Λ ⊆ ℤⁿ`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem A.6, p.13 (PDF 14), and the proof of Proposition A.2, p.12 (PDF 13)): positive integers
`s_1 ∣ s_2 ∣ ⋯ ∣ s_r` such that, for some basis `b_1, …, b_n` of `ℤⁿ`,
`Λ = ℤ s_1 b_1 ⊕ ⋯ ⊕ ℤ s_r b_r`. Equivalently `ℤⁿ/Λ ≅ ℤ^{n−r} ⊕ ⨁ ℤ/s_iℤ`, and `r = rank Λ`; the list
(with its leading ones) is the diagonal of the Smith normal form of any generating matrix of `Λ`, hence
is unique.

**Formalization Note** The list is indexed from `0`; `Fin.castLE` places the `i`-th invariant on the
`i`-th basis vector of `ℤⁿ`. -/
def IsSmithInvariants {n : ℕ} (Λ : Submodule ℤ (Fin n → ℤ)) (s : List ℕ) : Prop :=
  (∀ a ∈ s, 0 < a) ∧ s.IsChain (· ∣ ·) ∧
    ∃ h : s.length ≤ n, ∃ b : Module.Basis (Fin n) ℤ (Fin n → ℤ),
      Λ = Submodule.span ℤ (Set.range fun i : Fin s.length => (s.get i : ℤ) • b (Fin.castLE h i))

end IntADSat.Supplement


