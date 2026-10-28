-- Prove2me | Definitions.Def_WildeQIT_partialTrace
-- name    : WildeQIT_partialTrace
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:51:20.358204+00:00
-- url     : https://prove2.me/theorems/671946b0-3f61-4844-83c8-b9810be3e86e
-- title:
--   Partial trace $\mathrm{Tr}_B\{X_{AB}\}$ and $\mathrm{Tr}_A\{X_{AB}\}$
-- statement:
--   **Definition 4.3.4 (Partial Trace).** Let $X_{AB}$ be a square operator acting on a tensor product Hilbert space $\mathcal{H}_A \otimes \mathcal{H}_B$, and let $\{|l\rangle_B\}$ be an orthonormal basis for $\mathcal{H}_B$. Then the partial trace over the Hilbert space $\mathcal{H}_B$ is defined as
--
--   $$
--   \mathrm{Tr}_B\{X_{AB}\} \equiv \sum_l \left(I_A \otimes \langle l|_B\right) X_{AB} \left(I_A \otimes |l\rangle_B\right) .
--   $$
--
--   Symmetrically, $\mathrm{Tr}_A\{X_{AB}\} \equiv \sum_i (\langle i|_A \otimes I_B) X_{AB} (|i\rangle_A \otimes I_B)$ for an orthonormal basis $\{|i\rangle_A\}$ of $\mathcal{H}_A$. The partial trace produces the local (reduced) density operator $\rho_A = \mathrm{Tr}_B\{\rho_{AB}\}$ of a bipartite state, and is the operation under which the trace distance is monotone (Corollary 9.1.2).
--
--   **Formalization Note.** A bipartite operator is a matrix `X : Matrix (a × b) (a × b) ℂ` indexed by the product type (Mathlib's Kronecker convention `⊗ₖ`), and the orthonormal basis $\{|l\rangle_B\}$ is the standard basis of `b`. Then `WildeQIT.partialTraceRight X : Matrix a a ℂ` is $\mathrm{Tr}_B\{X\}$ with entries $(\mathrm{Tr}_B X)_{i,j} = \sum_{k} X_{(i,k),(j,k)}$, and `WildeQIT.partialTraceLeft X : Matrix b b ℂ` is $\mathrm{Tr}_A\{X\}$ with entries $(\mathrm{Tr}_A X)_{k,l} = \sum_{i} X_{(i,k),(i,l)}$. Only the traced-out factor is required to be finite.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §4.3.4 "Local Density Operators and Partial Trace", Definition 4.3.4 (Partial Trace).

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §4.3.4, Definition 4.3.4 (Partial Trace).

"Let `X_{AB}` be a square operator acting on a tensor product Hilbert space `ℋ_A ⊗ ℋ_B`, and let
`{|l⟩_B}` be an orthonormal basis for `ℋ_B`. Then the partial trace over the Hilbert space `ℋ_B`
is defined as `Tr_B{X_{AB}} ≡ ∑_l (I_A ⊗ ⟨l|_B) X_{AB} (I_A ⊗ |l⟩_B)`."

A bipartite operator is a matrix indexed by the product type `a × b` (the Kronecker convention
of Mathlib's `⊗ₖ`), and the orthonormal basis `{|l⟩_B}` is the standard basis of `b`.
-/

namespace WildeQIT

/-- **Definition 4.3.4 (Partial Trace over the right factor `B`).** For
`X : Matrix (a × b) (a × b) ℂ`, `Tr_B{X}` is the `a × a` matrix with entries
`(Tr_B X)ᵢⱼ = ∑ₖ X₍ᵢ,ₖ₎,₍ⱼ,ₖ₎`. -/
def partialTraceRight {a b : Type} [Fintype b] (X : Matrix (a × b) (a × b) ℂ) : Matrix a a ℂ :=
  Matrix.of fun i j => ∑ k, X (i, k) (j, k)

/-- **Definition 4.3.4 (Partial Trace over the left factor `A`).** For
`X : Matrix (a × b) (a × b) ℂ`, `Tr_A{X}` is the `b × b` matrix with entries
`(Tr_A X)ₖₗ = ∑ᵢ X₍ᵢ,ₖ₎,₍ᵢ,ₗ₎`. -/
def partialTraceLeft {a b : Type} [Fintype a] (X : Matrix (a × b) (a × b) ℂ) : Matrix b b ℂ :=
  Matrix.of fun k l => ∑ i, X (i, k) (i, l)

end WildeQIT


