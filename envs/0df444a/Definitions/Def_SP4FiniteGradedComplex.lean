-- Prove2me | Definitions.Def_SP4FiniteGradedComplex
-- name    : SP4FiniteGradedComplex
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T03:59:33.852288+00:00
-- url     : https://prove2.me/theorems/c7f3ac3c-57e7-4798-ba4e-6c971ee2489d
-- title:
--   Finite graded complexes with actual differential and quotient homology
-- statement:
--   Let $K$ be a field, $I$ an index set, and $C_i$ a family of $K$-vector spaces. The data consist of a permutation $\sigma$ of $I$, integer grades $g(i)$, and actual linear maps $d_i:C_i\to C_{\sigma i}$ satisfying $d_{\sigma i}d_i=0$ and $d_i\ne0\Rightarrow g(\sigma i)=g(i)-1$. Distinct indices may have the same grade. The interface defines the incoming map into cycles, the quotient homology $H_{\sigma i}=\ker d_{\sigma i}/\operatorname{im}d_i$, the total endomorphism with $(Dx)_{\sigma i}=d_i(x_i)$, and the polynomial sums of actual chain dimensions, homology dimensions, and differential ranks. The polynomial sums require $I$ finite; finite-dimensionality is imposed by the subsequent theorem. This is a linear-algebra interface, not a Floer complex realization or a theorem covering all library chain-complex presentations.
--
--   **Formalization Note.** The definitions do not assume finite-dimensionality. Their numerical coefficients use the finite-rank function, which equals the dimension for a finite-dimensional space and is zero for an infinite-dimensional space. The theorem imposes finite-dimensionality everywhere it interprets these numbers as dimensions.
--
--   $$
--   H_{\sigma i}=\ker d_{\sigma i}/\operatorname{im}d_i,\qquad (Dx)_{\sigma i}=d_i(x_i).
--   $$
-- source:
--   Local research note outputs/cycle18_structural_primary_proof.md, Section 1, A rank-polynomial identity for arbitrary matrices: the displayed degreewise dimension identity, P_C=P_H+(1+q^-1)Q, Q(1)=rank(d), and saturation implication. Formalized for actual finite permutation-indexed graded complexes; no Floer or common-coarsening realization is included. Primary source SHA-256 68da60b83072393fd9491dae22acb095ffce76a18a1285658417457df46188e4.

import Definitions.Def_SP4GradedLaurent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
open scoped BigOperators

namespace SP4FiniteGradedComplex

variable (K : Type*) [Field K] (I : Type*) (C : I → Type*)
  [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]

/-- Actual homogeneous differential blocks on a finite family (finiteness
is imposed by theorem hypotheses). Grades need not distinguish summands.
Only a nonzero block must lower the integer grade by one. -/
structure Data where
  prev : I ≃ I
  degree : I → ℤ
  d : ∀ i, C i →ₗ[K] C (prev i)
  square_zero : ∀ i, (d (prev i)).comp (d i) = 0
  lowers_degree : ∀ i, d i ≠ 0 → degree (prev i) = degree i - 1

variable {K I C}

/-- The actual incoming differential, with codomain restricted to cycles. -/
def incoming (A : Data K I C) (i : I) : C i →ₗ[K] LinearMap.ker (A.d (A.prev i)) :=
  (A.d i).codRestrict _ (by
    intro x
    change A.d (A.prev i) (A.d i x) = 0
    exact congrArg (fun f : C i →ₗ[K] C (A.prev (A.prev i)) => f x) (A.square_zero i))

/-- Homology at the target index `prev i`: cycles modulo actual boundaries. -/
abbrev HomologyAtTarget (A : Data K I C) (i : I) :=
  LinearMap.ker (A.d (A.prev i)) ⧸ LinearMap.range (incoming A i)

/-- The total endomorphism of the finite product, with the correct output
coordinate permutation. This is an actual map, not a sum of rank numbers. -/
def totalD (A : Data K I C) : (∀ i, C i) →ₗ[K] (∀ i, C i) :=
  (LinearEquiv.piCongrLeft K C A.prev).toLinearMap.comp (LinearMap.piMap A.d)

noncomputable def blockRank (A : Data K I C) (i : I) : ℕ :=
  Module.finrank K (LinearMap.range (A.d i))

noncomputable def chainPolynomial [Fintype I] (A : Data K I C) : SP4GradedLaurent.GradedPolynomial :=
  ∑ i, Finsupp.single (A.degree i) (Module.finrank K (C i) : ℤ)

noncomputable def homologyPolynomial [Fintype I] (A : Data K I C) : SP4GradedLaurent.GradedPolynomial :=
  ∑ i, Finsupp.single (A.degree (A.prev i)) (Module.finrank K (HomologyAtTarget A i) : ℤ)

noncomputable def rankPolynomial [Fintype I] (A : Data K I C) : SP4GradedLaurent.GradedPolynomial :=
  ∑ i, Finsupp.single (A.degree i) (blockRank A i : ℤ)

end SP4FiniteGradedComplex


