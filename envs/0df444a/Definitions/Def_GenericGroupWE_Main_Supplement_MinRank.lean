-- Prove2me | Definitions.Def_GenericGroupWE_Main_Supplement_MinRank
-- name    : GenericGroupWE_Main_Supplement_MinRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:07:24.276041+00:00
-- url     : https://prove2.me/theorems/d8c76b3f-4e0a-4276-921b-b00b3eb7e614
-- title:
--   Bounded-factor MinRank instances, their promises, and their output encoding
-- statement:
--   An instance of **bounded-factor MinRank** is a triple $(m, p, (M_1,\dots,M_k))$: a matrix order $m\in\mathbb N$, a prime $p$, and a finite list of matrices $M_j\in\mathbb F_p^{m\times m}$, where $\mathbb F_p=\mathbb Z/p\mathbb Z$. The list describes the linear space $S=\operatorname{span}_{\mathbb F_p}\{M_1,\dots,M_k\}$, whose elements are the combinations $\sum_j a_jM_j$ with $a\in\mathbb F_p^k$.
--
--   Three predicates are defined on instances.
--
--   1. **Well-formed**: $m\ge 4$, $2^m\le p<2^{m+1}$, and $M_1,\dots,M_k$ are linearly independent over $\mathbb F_p$, so that the list is a basis of $S$ (the empty list, i.e. $S=\{0\}$, is allowed).
--   2. **YES instance**: $S$ contains a nonzero matrix $uv^{\mathsf T}$ with $u\in\mathbb F_p^m$ arbitrary and $v\in\{0,1\}^m$; that is, for some coefficient vector $a$, $\sum_j a_jM_j=uv^{\mathsf T}\neq 0$ and every coordinate of $v$ is $0$ or $1$.
--   3. **NO instance** (for a real constant $c>0$): every nonzero matrix of $S$ has rank at least $(\log_2 m)^c$, ranks taken over $\mathbb F_p$.
--
--   The output of a reduction is the instance written in the base mission's bit encoding of $(m,p,k)$ followed by all matrix entries, as the halting output of a group-free oracle program.
--
--   These are the two cases of the promise problem in Theorem 1.2. When $m\ge4$ and $c>0$ we have $(\log_2 m)^c\ge 2^c>1$, so no well-formed instance is both a YES and a NO instance.
--
--   **Formalization Note** The window $2^m\le p<2^{m+1}$ is how the paper's proof (§7) realizes "primes $p=\Theta(2^m)$". The matrices form a `MatrixBundle m p` from the published scheme definitions; ranks are `Matrix.rank` over `ZMod p`, logarithms `Real.logb 2` with a real exponent.
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, Theorem 1.2, PDF pp. 2–3 (printed pp. 1–2); §2 conventions (ranks over F_p, bases linearly independent, Boolean vectors), PDF p. 7 (printed p. 6); §7, Randomized MinRank Hardness, PDF p. 31 (printed p. 30).

import Definitions.Def_GenericGroupWE_Main_Scheme

namespace GenericGroupWE.Main.Supplement

/-- Hair--Sahai, STOC 2027 submission 47, Theorem 1.2, PDF pp. 2–3: an instance of
bounded-factor MinRank is a matrix order `m`, a prime `p`, and a list of matrices in
`F_p^{m×m}` meant as a basis of the space `S` it spans. -/
structure MinRankInstance where
  m : ℕ
  p : PrimeOrder
  bundle : MatrixBundle m p

/-- The instance promises shared by both cases of Theorem 1.2: `m ≥ 4`, the prime lies in
`[2^m, 2^(m+1))` (the window §7, PDF p. 31, produces for `p = Θ(2^m)`), and the listed matrices
are linearly independent over `F_p` (the space is given by a basis; the empty list, i.e. the zero
space, is allowed). -/
def MinRankInstance.WellFormed (I : MinRankInstance) : Prop :=
  4 ≤ I.m ∧ 2 ^ I.m ≤ I.p.val ∧ I.p.val < 2 ^ (I.m + 1) ∧
    LinearIndependent (ZMod I.p.val) I.bundle.matrices

/-- Case 1 of Theorem 1.2: the span contains a nonzero matrix `u vᵀ` with `v ∈ {0,1}^m`
(`u` arbitrary). -/
def MinRankInstance.IsYes (I : MinRankInstance) : Prop :=
  ∃ a : Fin I.bundle.k → ZMod I.p.val, ∃ u v : Fin I.m → ZMod I.p.val,
    I.bundle.combination a = Matrix.vecMulVec u v ∧ Matrix.vecMulVec u v ≠ 0 ∧
      ∀ i, v i = 0 ∨ v i = 1

/-- Case 2 of Theorem 1.2: every nonzero matrix of the span has rank at least `(log₂ m)^c`. -/
def MinRankInstance.IsNo (c : ℝ) (I : MinRankInstance) : Prop :=
  ∀ a : Fin I.bundle.k → ZMod I.p.val, I.bundle.combination a ≠ 0 →
    (Real.logb 2 (I.m : ℝ)) ^ c ≤ ((I.bundle.combination a).rank : ℝ)

/-- The output string of a reduction: the base mission's encoding of `(m, p, k, matrices)`,
as the halting output of a group-free oracle program. -/
noncomputable def MinRankInstance.output (I : MinRankInstance) : Ciphertext :=
  ⟨none, some (bundleBits I.bundle)⟩

end GenericGroupWE.Main.Supplement


