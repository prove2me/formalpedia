-- Prove2me | Definitions.Def_OAIQ129G010
-- name    : OAIQ129G010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:36:35.126569+00:00
-- url     : https://prove2.me/theorems/d43eaa80-3cc4-4bdb-9239-8d7c7bfaa3b4
-- title:
--   Definitions bundle OAIQ129G010 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 2 definitions and 57 theorems. The definitions and types are `OAI.Generator.Tracial.CornerPartition.joint`, `OAI.Generator.Tracial.traceFreeTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_NormalDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalDimension.lean), [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_SpectralApproximation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralApproximation.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean), [`FactorGeneration_SpectralStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralStates.lean).
--
--   **Imports.** It imports the bundles `OAIQ129G007` and `OAIQ129G008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G013` and `OAIQ129G014`; the proofs of `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget_q129` and `OAI.Generator.Tracial.exists_normal_matrix_approximation_q129`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G007
import Definitions.Def_OAIQ129G008

section
-- module Solutions.OAIQ129_RG2.Compat
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
end OAIVecTail
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Every nonzero projection eventually fails to fit into the dyadic corners. -/
theorem traceFree_exists_dyadic_obstruction
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ¬r.Subequivalent (traceFreeDyadicReference hfactor hdiff p n) := by
  by_contra hn
  exact hr (traceFree_dyadic_archimedean hfactor hdiff hfinite p r
    (by simpa only [not_exists,not_not] using hn))

/-- Every nonzero projection contains an equivalent copy of every sufficiently
small dyadic reference piece. This supplies the positivity input for dimension. -/
theorem traceFree_eventually_dyadic_subequivalent
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p r : AlgebraProjection M) (hr : r.val≠0) :
    ∃ n, ∀ m, n ≤ m → (traceFreeDyadicReference hfactor hdiff p m).Subequivalent r := by
  obtain ⟨n,hn⟩ := traceFree_exists_dyadic_obstruction hfactor hdiff hfinite p r hr
  have he : (traceFreeDyadicReference hfactor hdiff p n).Subequivalent r :=
    (AlgebraProjection.subequivalent_total hfactor r _).resolve_left hn
  refine ⟨n,fun m hm => ?_⟩
  exact AlgebraProjection.subequivalent_trans (AlgebraProjection.subequivalent_of_le
    (traceFreeDyadicReference_antitone hfactor hdiff p hm)) he

end Tracial

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Archimedean comparison makes the supremum strictly positive on nonzero projections. -/
theorem traceFreeDyadicSup_pos
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hq : q.val≠0) :
    0 < traceFreeDyadicSup hfactor hdiff p q := by
  obtain ⟨n,hn⟩ := traceFree_eventually_dyadic_subequivalent hfactor hdiff hfinite p q hq
  have h := hn n le_rfl
  have he : ((traceFreeDyadicPartition hfactor hdiff p n).subset {dyadicFalseIndex n}).Subequivalent q := by
    rw [EquivalentPartition.subset_singleton]
    exact h
  apply lt_of_lt_of_le ?_ (traceFreeDyadicSup_lower_bound hfactor hdiff p q n _ he)
  simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  exact div_pos zero_lt_one (pow_pos (by norm_num) _)

theorem traceFreeDyadicSup_eq_zero_iff
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hp : p.val≠0) :
    traceFreeDyadicSup hfactor hdiff p q=0 ↔ q.val=0 := by
  constructor
  · intro h
    by_contra hq
    have hh := traceFreeDyadicSup_pos hfactor hdiff hfinite p q hq
    rw [h] at hh
    exact lt_irrefl _ hh
  · exact traceFreeDyadicSup_zero hfactor hdiff p q hp

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Faithfulness and additivity give strict increase along proper inclusion. -/
theorem traceFreeDyadicSup_strictMono
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hrp : r ≤ p) (hqr : q < r) :
    traceFreeDyadicSup hfactor hdiff p q < traceFreeDyadicSup hfactor hdiff p r := by
  have hle : q ≤ r := le_of_lt hqr
  let s := AlgebraProjection.remainder q r hle
  have hs : s.val≠0 := by
    change r.val-q.val≠0
    intro h
    exact (ne_of_lt hqr) (Subtype.ext (sub_eq_zero.mp h).symm)
  have hpos := traceFreeDyadicSup_pos hfactor hdiff hfinite p s hs
  have he := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite p q s hp
    (hle.trans hrp) ((AlgebraProjection.remainder_le q r hle).trans hrp)
    (AlgebraProjection.remainder_orthogonal q r hle)
  rw [AlgebraProjection.orthogonalSum_remainder] at he
  linarith

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFree_target_eq_of_dimension_le
    (p q : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p)
    (v : PartialIsometry M) (ht : v.target ≤ q)
    (hd : traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p v.support) :
    v.target=q := by
  by_contra he
  have hlt := traceFreeDyadicSup_strictMono hfactor hdiff hfinite p v.target q hp hqp
    (lt_of_le_of_ne ht he)
  have heq := traceFreeDyadicSup_equivalent hfactor hdiff p
    (show v.support.Equivalent v.target from ⟨v,rfl,rfl⟩)
  linarith

include hfinite in
/-- Real-valued comparison is exactly witnessed projection subequivalence. -/
theorem traceFreeDyadicSup_le_iff_subequivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q ≤ traceFreeDyadicSup hfactor hdiff p r ↔
      q.Subequivalent r := by
  refine ⟨fun hd => ?_,traceFreeDyadicSup_mono hfactor hdiff p⟩
  rcases AlgebraProjection.subequivalent_total hfactor q r with h | h
  · exact h
  · obtain ⟨v,hv,ht⟩ := h
    have he : v.target=q := traceFree_target_eq_of_dimension_le hfactor hdiff hfinite
      p q hp hqp v ht (by rw [hv]; exact hd)
    exact ⟨v.adjoint,he,le_of_eq (v.adjoint_target.trans hv)⟩

include hfinite in
theorem traceFreeDyadicSup_eq_iff_equivalent
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r ↔
      q.Equivalent r := by
  constructor
  · intro h
    exact AlgebraProjection.equivalent_of_mutual_subequivalent hfinite
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p q r hp hqp).mp (le_of_eq h))
      ((traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite p r q hp hrp).mp (le_of_eq h.symm))
  · exact traceFreeDyadicSup_equivalent hfactor hdiff p

end Tracial

end

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_le_iff_subequivalent
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (q r : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ traceFreeDimension hfactor hdiff r ↔
      q.Subequivalent r :=
  traceFreeDyadicSup_le_iff_subequivalent hfactor hdiff hfinite _ q r hunit (one_mul _)

include hfinite in
theorem traceFreeDimension_strictMono (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    StrictMono (traceFreeDimension hfactor hdiff) :=
  fun _ _ h => traceFreeDyadicSup_strictMono hfactor hdiff hfinite _ _ _ hunit (one_mul _) h

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Continuity on sequences follows from compatible embeddings into each
concrete dyadic upper approximant of the real supremum. -/
theorem traceFreeDimension_isLUB_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (q : ℕ → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n))) := by
  let c := sSup (Set.range (fun n => traceFreeDimension hfactor hdiff (q n)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hne := Set.range_nonempty (fun n => traceFreeDimension hfactor hdiff (q n))
  have hqc (n : ℕ) : traceFreeDimension hfactor hdiff (q n) ≤ c := le_csSup hb ⟨n,rfl⟩
  have hc : 0 ≤ c := (traceFreeDimension_nonneg hfactor hdiff (q 0)).trans (hqc 0)
  have hc1 : c ≤ 1 := csSup_le hne (by
    rintro _ ⟨n,rfl⟩; exact traceFreeDimension_le_one hfactor hdiff (q n))
  apply le_antisymm ?_ (csSup_le hne (by
    rintro _ ⟨n,rfl⟩
    exact traceFreeDimension_mono hfactor hdiff (hp.1 ⟨n,rfl⟩)))
  apply le_of_all_dyadic_errors
  intro n
  obtain ⟨r,hcr,hrc⟩ := traceFreeDimension_exists_upper hfactor hdiff hfinite hunit c hc hc1 n
  have hqr (k : ℕ) : (q k).Subequivalent r :=
    (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit _ _).mp
      ((hqc k).trans hcr)
  exact (traceFreeDimension_subequivalent hfactor hdiff
    (AlgebraProjection.isLUB_subequivalent_of_sequence hfactor hfinite q hq p hp r hqr)).trans hrc

include hfinite in
/-- Construct an increasing countable subfamily whose supremum dimension is
the real supremum of the entire directed family. No countability is assumed. -/
theorem traceFreeDimension_exists_exhausting_sequence
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ (a : ℕ → I) (s : AlgebraProjection M), Monotone a ∧
      IsLUB (Set.range (fun n => q (a n))) s ∧
      traceFreeDimension hfactor hdiff s =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  classical
  let c := sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i)))
  have hb := traceFreeDimension_range_bddAbove hfactor hdiff q
  have hqc (i : I) : traceFreeDimension hfactor hdiff (q i) ≤ c := le_csSup hb ⟨i,rfl⟩
  have hex (n : ℕ) : ∃ i, c-1/2^n < traceFreeDimension hfactor hdiff (q i) := by
    have hn : c-1/2^n < c := sub_lt_self c (by positivity)
    obtain ⟨_,⟨i,rfl⟩,hi⟩ := exists_lt_of_lt_csSup
      (Set.range_nonempty (fun i => traceFreeDimension hfactor hdiff (q i))) hn
    exact ⟨i,hi⟩
  choose f hf using hex
  obtain ⟨a,ha,hfa,_⟩ := exists_monotone_dominating_from f (Classical.choice ‹Nonempty I›)
  obtain ⟨s,hs⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (a n)) (hq.comp ha)
  refine ⟨a,s,ha,hs,le_antisymm ?_ ?_⟩
  · rw [traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp ha) s hs]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨n,rfl⟩; exact hqc (a n))
  · apply le_of_all_dyadic_errors
    intro n
    have hfq := traceFreeDimension_mono hfactor hdiff (hq (hfa n))
    have hqs := traceFreeDimension_mono hfactor hdiff (hs.1 ⟨n,rfl⟩)
    have hfn := hf n
    linarith

include hfinite in
/-- The constructed countable supremum bounds the entire net: adjoining any
one index cannot increase its dimension, so strict increase forces equality. -/
theorem traceFreeDimension_exists_isLUB
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q) :
    ∃ p : AlgebraProjection M, IsLUB (Set.range q) p ∧
      traceFreeDimension hfactor hdiff p =
        sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨a,s,ha,hs,hd⟩ := traceFreeDimension_exists_exhausting_sequence
    hfactor hdiff hfinite hunit q hq
  have hupper (i : I) : q i ≤ s := by
    obtain ⟨b,hb,hab,hib⟩ := exists_monotone_dominating_from a i
    obtain ⟨t,ht⟩ := AlgebraProjection.exists_isLUB_monotone (fun n => q (b n)) (hq.comp hb)
    have hst : s ≤ t := hs.2 (by
      rintro _ ⟨n,rfl⟩; exact (hq (hab n)).trans (ht.1 ⟨n,rfl⟩))
    have htd : traceFreeDimension hfactor hdiff t ≤ traceFreeDimension hfactor hdiff s := by
      rw [hd,traceFreeDimension_isLUB_sequence hfactor hdiff hfinite hunit _ (hq.comp hb) t ht]
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨n,rfl⟩
      exact le_csSup (traceFreeDimension_range_bddAbove hfactor hdiff q) ⟨b n,rfl⟩
    have he : s=t := by
      by_contra hne
      exact (not_lt_of_ge htd) (traceFreeDimension_strictMono hfactor hdiff hfinite hunit
        (lt_of_le_of_ne hst hne))
    rw [he]
    exact (hq (hib 0)).trans (ht.1 ⟨0,rfl⟩)
  refine ⟨s,⟨?_,?_⟩,hd⟩
  · rintro _ ⟨i,rfl⟩; exact hupper i
  · intro p hp
    exact hs.2 (by rintro _ ⟨n,rfl⟩; exact hp ⟨a n,rfl⟩)

include hfinite in
/-- Order continuity on arbitrary nonempty directed projection nets. -/
theorem traceFreeDimension_isLUB_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    traceFreeDimension hfactor hdiff p =
      sSup (Set.range (fun i => traceFreeDimension hfactor hdiff (q i))) := by
  obtain ⟨s,hs,hd⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit q hq
  have he : p=s := le_antisymm (hp.2 hs.1) (hs.2 hp.1)
  rw [he]
  exact hd

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_exists_small_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (hp : p.val≠0) (ε : ℝ) (hε : 0<ε) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ 0 < traceFreeDimension hfactor hdiff q ∧
      traceFreeDimension hfactor hdiff q < ε := by
  classical
  have hpD : 0 < traceFreeDimension hfactor hdiff p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite _ p hp
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (lt_min hε hpD) (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : (0 : ℝ)<1/2^n := by positivity
  have hi : Nonempty (DyadicIndex n) := Fintype.card_pos_iff.mp (by
    rw [card_dyadicIndex]; positivity)
  let i : DyadicIndex n := Classical.choice hi
  let e := (traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i}
  have heD : traceFreeDimension hfactor hdiff e=1/2^n := by
    change traceFreeDyadicSup hfactor hdiff ⟨1,IsStarProjection.one _⟩
      ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset {i})=1/2^n
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ hunit]
    simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit e p).mp
    (by rw [heD]; exact (lt_min_iff.mp hn).2.le)
  have he : traceFreeDimension hfactor hdiff v.target=1/2^n := by
    have h := traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show e.Equivalent v.target from ⟨v,hv,rfl⟩)
    exact h.symm.trans heD
  exact ⟨v.target,ht,by rw [he]; exact hn0,by rw [he]; exact (lt_min_iff.mp hn).1⟩

include hfinite in
theorem traceFreeDimension_bounded_chain
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Set (AlgebraProjection M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (d : ℝ)
    (hp : ∀ q ∈ c, q ≤ p) (hd : ∀ q ∈ c, traceFreeDimension hfactor hdiff q ≤ d) :
    ∃ q : AlgebraProjection M, (∀ r ∈ c, r ≤ q) ∧ q ≤ p ∧
      traceFreeDimension hfactor hdiff q ≤ d := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨q,hq,hD⟩ := traceFreeDimension_exists_isLUB hfactor hdiff hfinite hunit
    (fun r : c => r.val) (fun _ _ h => h)
  refine ⟨q,fun r hr => hq.1 ⟨⟨r,hr⟩,rfl⟩,?_,?_⟩
  · exact hq.2 (by rintro _ ⟨r,rfl⟩; exact hp r.val r.property)
  · rw [hD]
    exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨r,rfl⟩; exact hd r.val r.property)

include hfinite in
theorem traceFreeDimension_exists_maximal_below
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d ∧
      ∀ r : AlgebraProjection M, r ≤ p → traceFreeDimension hfactor hdiff r ≤ d →
        q ≤ r → r ≤ q := by
  let S : Set (AlgebraProjection M) := {q | q ≤ p ∧ traceFreeDimension hfactor hdiff q ≤ d}
  obtain ⟨q,hq⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨q,hcq,hqp,hqd⟩ := traceFreeDimension_bounded_chain hfactor hdiff hfinite hunit
        c hchain hne p d (fun q hq => (hc hq).1) (fun q hq => (hc hq).2)
      exact ⟨q,⟨hqp,hqd⟩,hcq⟩
    · refine ⟨⟨0,IsStarProjection.zero _⟩,⟨mul_zero _,?_⟩,?_⟩
      · have hz := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩
          ⟨0,IsStarProjection.zero _⟩ hunit rfl
        exact hz.le.trans hd
      · intro r hr
        exact (hne ⟨r,hr⟩).elim)
  exact ⟨q,hq.1.1,hq.1.2,fun r hr hrd hqr => hq.2 ⟨hr,hrd⟩ hqr⟩

include hfinite in
/-- Every dimension between zero and D(p) is realized inside p. -/
theorem traceFreeDimension_exists_subprojection
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) (d : ℝ) (hd : 0 ≤ d)
    (hdp : d ≤ traceFreeDimension hfactor hdiff p) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ traceFreeDimension hfactor hdiff q=d := by
  obtain ⟨q,hqp,hqd,hmax⟩ := traceFreeDimension_exists_maximal_below
    hfactor hdiff hfinite hunit p d hd
  refine ⟨q,hqp,le_antisymm hqd ?_⟩
  by_contra hnot
  have hlt : traceFreeDimension hfactor hdiff q < d := lt_of_not_ge hnot
  let r := AlgebraProjection.remainder q p hqp
  have hr : r.val≠0 := by
    change p.val-q.val≠0
    intro hz
    have he : p=q := Subtype.ext (sub_eq_zero.mp hz)
    rw [he] at hdp
    exact (not_lt_of_ge hdp) hlt
  obtain ⟨s,hs,hpos,hsmall⟩ := traceFreeDimension_exists_small_subprojection
    hfactor hdiff hfinite hunit r hr (d-traceFreeDimension hfactor hdiff q) (sub_pos.mpr hlt)
  have ho : q.val*s.val=0 :=
    projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl hs
  let t := orthogonalSum q s ho
  have htp : t ≤ p := orthogonalSum_le ho hqp (hs.trans (AlgebraProjection.remainder_le q p hqp))
  have htD : traceFreeDimension hfactor hdiff t=
      traceFreeDimension hfactor hdiff q+traceFreeDimension hfactor hdiff s :=
    traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q s
      hunit (one_mul _) (one_mul _) ho
  have htd : traceFreeDimension hfactor hdiff t ≤ d := by rw [htD]; linarith
  have hle : t ≤ q := hmax t htp htd (le_orthogonalSum_left _ _ ho)
  have hmono := traceFreeDimension_mono hfactor hdiff hle
  rw [htD] at hmono
  linarith

end

/-! Finite partitions with prescribed dimensions, and actual equivalent
partitions of arbitrary positive finite size in every corner. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Every prescribed finite list of nonnegative dimensions summing to D(p)
is realized by pairwise orthogonal actual projections summing to p. -/
theorem traceFreeDimension_exists_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (p : AlgebraProjection M) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i=traceFreeDimension hfactor hdiff p) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧ (∀ i, traceFreeDimension hfactor hdiff (q i)=d i) := by
  induction n generalizing p with
  | zero =>
    have hpD : traceFreeDimension hfactor hdiff p=0 := by simpa using hsum.symm
    have hpz : p.val=0 := (traceFreeDyadicSup_eq_zero_iff hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hunit).mp hpD
    refine ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i⟩
    simpa using hpz.symm
  | succ n ih =>
    have hsum' : d 0+∑ i : Fin n, d i.succ=traceFreeDimension hfactor hdiff p := by
      simpa only [Fin.sum_univ_succ] using hsum
    have hdp : d 0 ≤ traceFreeDimension hfactor hdiff p := by
      have hh : 0 ≤ ∑ i : Fin n, d i.succ := Finset.sum_nonneg (fun i _ => hd i.succ)
      linarith
    obtain ⟨q,hqp,hqd⟩ := traceFreeDimension_exists_subprojection
      hfactor hdiff hfinite hunit p (d 0) (hd 0) hdp
    let r := AlgebraProjection.remainder q p hqp
    have hrD : traceFreeDimension hfactor hdiff r=
        traceFreeDimension hfactor hdiff p-d 0 := by
      rw [traceFreeDimension_remainder hfactor hdiff hfinite hunit q p hqp,hqd]
    obtain ⟨b,hbr,hbo,hbs,hbd⟩ := ih r (fun i => d i.succ) (fun i => hd i.succ) (by
      rw [hrD]; linarith)
    let a : Fin (n+1) → AlgebraProjection M := Fin.cons q b
    have hqb (i : Fin n) : q.val*(b i).val=0 :=
      projection_orthogonal_of_le (AlgebraProjection.remainder_orthogonal q p hqp) le_rfl (hbr i)
    refine ⟨a,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases hqp (fun j => ?_) i
      exact (hbr j).trans (AlgebraProjection.remainder_le q p hqp)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro h; exact (h rfl).elim
        · intro _; exact hqb l
      · intro k
        refine Fin.cases ?_ (fun l => ?_) k
        · intro _; exact PartialIsometry.orthogonal_reverse q (b j) (hqb j)
        · intro h
          exact hbo j l (fun he => h (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      change q.val+(∑ i, (b i).val)=p.val
      rw [hbs]
      change q.val+(p.val-q.val)=p.val
      abel
    · intro i
      exact Fin.cases hqd hbd i

include hfinite in
/-- A finite corner partition into n equal dimensions, for every n>0. -/
theorem traceFreeDimension_exists_uniform_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    ∃ q : Fin n → AlgebraProjection M, (∀ i, q i ≤ p) ∧
      (∀ i j, i≠j → (q i).val*(q j).val=0) ∧
      (∑ i, (q i).val)=p.val ∧
      (∀ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p/n) := by
  apply traceFreeDimension_exists_partition hfactor hdiff hfinite hunit n p
    (fun _ => traceFreeDimension hfactor hdiff p/n)
  · intro i
    exact div_nonneg (traceFreeDimension_nonneg hfactor hdiff p) (Nat.cast_nonneg n)
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

include hfactor hdiff hfinite in
/-- Actual matrix-unit legs for a partition of every positive finite size. -/
theorem traceFreeDimension_exists_equivalent_partition
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (n : ℕ) (hn : 0<n) (p : AlgebraProjection M) :
    Nonempty (EquivalentPartition p (Fin n)) := by
  classical
  obtain ⟨q,hqp,hqo,hqs,hqd⟩ := traceFreeDimension_exists_uniform_partition
    hfactor hdiff hfinite hunit n hn p
  let i₀ : Fin n := ⟨0,hn⟩
  have he (i : Fin n) : (q i₀).Equivalent (q i) :=
    (traceFreeDyadicSup_eq_iff_equivalent hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩
      (q i₀) (q i) hunit (one_mul _) (one_mul _)).mp ((hqd i₀).trans (hqd i).symm)
  choose v hv ht using he
  exact ⟨{
    base := q i₀
    leg := v
    initial := hv
    cross := fun i j hij => (v i).adjoint.mul_eq_zero (v j) (by
      change (v i).target.val*(v j).target.val=0
      rw [ht i,ht j]; exact hqo i j hij)
    total := by simpa only [ht] using hqs
    bound := fun i => by rw [ht]; exact hqp i }⟩

end Tracial

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

def joint : CornerPartition p := ofFamily (Q.jointPiece R hc)
  (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc)

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

end

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/
section
open Filter
open scoped BigOperators Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.unique
    {x : M.toStarSubalgebra} (hx : IsSelfAdjoint x) {s t : ℂ}
    (hs : IsDimensionSpectralValue hfactor hdiff x s)
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : s=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
  have hcomm := hQ x (Commute.refl x) (Commute.one_left x)
  have hs' := hs Q (fun i => (c i : ℂ)) hcomm
  have ht' := ht Q (fun i => (c i : ℂ)) hcomm
  simp only [one_mul,mul_one] at herr
  let w : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  have htri := dist_triangle s w t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev w t] at htri
  dsimp only [w] at htri
  have hnorm : ‖s-t‖ ≤ 2/2^n := by
    rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
    linarith
  simpa only [sub_zero,abs_of_nonneg (norm_nonneg _)] using hnorm

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ‖dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ ‖x‖ :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2.norm_le hfactor hdiff

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_eq_of_approximants
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℂ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℂ),
        (∀ i, Commute (Q.piece i).val x) ∧
        ‖x-∑ i, c i • (Q.piece i).val‖ < ε ∧
        ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ < ε) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hxerr,hterr⟩ := h (ε/2) (half_pos hε)
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2 Q c hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
    (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t] at htri
  linarith

theorem dimensionSpectralValue_real_smul
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (r : ℝ) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (r • x) ((IsSelfAdjoint.all r).smul hx)=
      (r : ℂ)*dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  apply dimensionSpectralValue_eq_of_approximants hfactor hdiff hfinite hunit
  intro ε hε
  have hr : 0 < ‖r‖+1 := by positivity
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/(‖r‖+1)) (div_pos hε hr)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have hb : ‖r‖*(ε/(‖r‖+1)) < ε := by
    have hh := (div_pos hε hr)
    have he : (‖r‖+1)*(ε/(‖r‖+1))=ε := mul_div_cancel₀ _ (ne_of_gt hr)
    nlinarith
  refine ⟨Q,fun i => (r : ℂ)*(c i : ℂ),?_,?_,?_⟩
  · intro i
    show (Q.piece i).val*(r • x)=(r • x)*(Q.piece i).val
    rw [mul_smul_comm,smul_mul_assoc,(hc i).eq]
  · have he : (r • x)-∑ i, ((r : ℂ)*(c i : ℂ)) • (Q.piece i).val=
        r • (x-∑ i, (c i : ℂ) • (Q.piece i).val) := by
      simp only [smul_sub,Finset.smul_sum,← smul_assoc,Complex.real_smul]
    rw [he,norm_smul]
    exact (mul_le_mul_of_nonneg_left herr.le (norm_nonneg r)).trans_lt hb
  · rw [show (∑ i, ((r : ℂ)*(c i : ℂ))*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
        (r : ℂ)*(∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) by
          rw [Finset.mul_sum]; simp only [mul_assoc],← mul_sub,norm_mul,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (hval.trans herr.le) (norm_nonneg r)).trans_lt hb

theorem dimensionSpectralValue_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    dimensionSpectralValue hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)=0 := by
  have h := dimensionSpectralValue_norm_le hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)
  rw [norm_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

theorem dimensionSpectralValue_neg (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (-x) hx.neg=
      -dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  simpa only [neg_one_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
    dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit (-1) x hx

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_add_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx+
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  classical
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herrQ⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/4) (by positivity)
  obtain ⟨R,d,_,hR,herrR⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ y hy (ε/4) (by positivity)
  simp only [one_mul,mul_one] at herrQ herrR
  have hQx := hQ x (Commute.refl x) (Commute.one_left x)
  have hQy := hQ y hxy (Commute.one_left y)
  have hRx := hR x hxy.symm (Commute.one_left x)
  have hRy := hR y (Commute.refl y) (Commute.one_left y)
  have hc (i : Fin Q.size) (j : Fin R.size) :
      Commute (Q.piece i).val (R.piece j).val :=
    (hR _ (hQy i).symm (Commute.one_left _) j).symm
  let q := Q.jointPiece R hc
  let b (a : Fin Q.size × Fin R.size) : ℂ := (c a.1 : ℂ)+(d a.2 : ℂ)
  let sx : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
  let sy : M.toStarSubalgebra := ∑ j, (d j : ℂ) • (R.piece j).val
  let wx : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  let wy : ℂ := ∑ j, (d j : ℂ)*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)
  have hsum : (∑ a, b a • (q a).val)=sx+sy := by
    simp only [b,add_smul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (Q.joint_sum_left R hc (fun i => (c i : ℂ)))
      (Q.joint_sum_right R hc (fun j => (d j : ℂ)))
  have hweight : (∑ a, b a*(traceFreeDimension hfactor hdiff (q a) : ℂ))=wx+wy := by
    simp only [b,add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·)
      (Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit (fun i => (c i : ℂ)))
      (Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit (fun j => (d j : ℂ)))
  have hcomm (a : Fin Q.size × Fin R.size) : Commute (q a).val (x+y) :=
    ((hQx a.1).mul_left (hRx a.2)).add_right ((hQy a.1).mul_left (hRy a.2))
  have hz := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (x+y) (hx.add hy)).2.family_bound
    hfactor hdiff q (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc) b hcomm
  rw [hsum,hweight] at hz
  have he : ‖(x+y)-(sx+sy)‖ ≤ ‖x-sx‖+‖y-sy‖ := by
    rw [show (x+y)-(sx+sy)=(x-sx)+(y-sy) by abel]
    exact norm_add_le _ _
  have hxv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hQx
  have hyv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit y hy).2
    R (fun j => (d j : ℂ)) hRy
  let vx := dimensionSpectralValue hfactor hdiff hfinite hunit x hx
  let vy := dimensionSpectralValue hfactor hdiff hfinite hunit y hy
  have hv : ‖(vx+vy)-(wx+wy)‖ ≤ ‖vx-wx‖+‖vy-wy‖ := by
    rw [show (vx+vy)-(wx+wy)=(vx-wx)+(vy-wy) by abel]
    exact norm_add_le _ _
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)) (wx+wy) (vx+vy)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (wx+wy) (vx+vy)] at htri
  change ‖vx-wx‖ ≤ ‖x-sx‖ at hxv
  change ‖vy-wy‖ ≤ ‖y-sy‖ at hyv
  change ‖x-sx‖ < ε/4 at herrQ
  change ‖y-sy‖ < ε/4 at herrR
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)-(vx+vy)‖ ≤ 0+ε
  linarith

theorem dimensionSpectralValue_sub_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x-y) (hx.sub hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx-
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  simpa only [sub_eq_add_neg,dimensionSpectralValue_neg hfactor hdiff hfinite hunit y hy] using
    dimensionSpectralValue_add_of_commute hfactor hdiff hfinite hunit x (-y) hx hy.neg hxy.neg_right

end

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem child_endpoints (hI : I.lo ≤ I.hi) (b : Bool) :
    I.lo ≤ (I.child hx b).lo ∧ (I.child hx b).lo ≤ (I.child hx b).hi ∧
      (I.child hx b).hi ≤ I.hi := by
  cases b <;> dsimp [child,low,high,midpoint]
  · exact ⟨le_rfl,by linarith,by linarith⟩
  · exact ⟨by linarith,by linarith,le_rfl⟩

theorem level_endpoints (hI : I.lo ≤ I.hi) : ∀ n i,
    I.lo ≤ (I.level hx n i).lo ∧ (I.level hx n i).lo ≤ (I.level hx n i).hi ∧
      (I.level hx n i).hi ≤ I.hi
  | 0,_ => ⟨le_rfl,hI,le_rfl⟩
  | n+1,i => by
    have h := level_endpoints hI n i.1
    have hchild := (I.level hx n i.1).child_endpoints hx h.2.1 i.2
    exact ⟨h.1.trans hchild.1,hchild.2.1,hchild.2.2.trans h.2.2⟩

end SpectralInterval

attribute [local instance] OAI.Generator.Tracial.spectralValueCStar
attribute [local instance] OAI.Generator.Tracial.spectralValueOrder
attribute [local instance] OAI.Generator.Tracial.spectralValuePreorder
attribute [local instance] OAI.Generator.Tracial.spectralValueLE
attribute [local instance] OAI.Generator.Tracial.spectralValueStarOrder
/-- A positive operator has arbitrarily accurate finite positive spectral
approximants preserving its entire commutant. -/
theorem exists_positive_spectral_approximation
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧
      (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I : SpectralInterval x :=
    { proj := ⟨1,IsStarProjection.one _⟩
      lo := 0
      hi := ‖x‖
      lower := by simpa only [one_mul,mul_one,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro y hy i
    exact I.partition_commutes hx.isSelfAdjoint hy (Commute.one_left y) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖1*x*1-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [one_mul,mul_one] using hn

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_spectral_approximation x hx ε hε
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2
    Q (fun i => (c i : ℂ)) (hQ x (Commute.refl x))
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
  have hw : 0 ≤ w := Finset.sum_nonneg (fun i _ => mul_nonneg (hc i)
    (traceFreeDimension_nonneg hfactor hdiff _))
  have he : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
  have hb : ‖t-(w : ℂ)‖ < ε := by rw [he]; exact hval.trans_lt herr
  have hre := Complex.re_le_norm ((w : ℂ)-t)
  rw [Complex.sub_re,Complex.ofReal_re,norm_sub_rev (w : ℂ) t] at hre
  change 0 ≤ t.re+ε
  linarith

theorem dimensionSpectralValue_mono_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) (hle : x ≤ y) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).re ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit y hy).re := by
  have h := dimensionSpectralValue_nonneg hfactor hdiff hfinite hunit (y-x) (sub_nonneg.mpr hle)
  rw [dimensionSpectralValue_sub_of_commute hfactor hdiff hfinite hunit y x hy hx hxy.symm,
    Complex.sub_re] at h
  exact sub_nonneg.mp h

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.spectralFaithfulCStar
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulOrder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulPreorder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulLE
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulStarOrder
theorem positive_spectral_cut_domination
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    (t : ℂ) • (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≤ x := by
  let p : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  let q := cornerSpectralCut p x t
  have hl : 0 ≤ q.val*x*q.val-(t : ℂ) • q.val := cornerSpectralCut_lower p x hx.isSelfAdjoint t
  have hr := star_left_conjugate_nonneg hx (1-q.val)
  rw [star_sub,star_one,q.property.isSelfAdjoint.star_eq] at hr
  have hsum := add_nonneg hl hr
  have he := cornerSpectralPartition_pinch p x hx.isSelfAdjoint t
  rw [cornerSpectralPartition,CornerPartition.binary_pinch] at he
  change q.val*x*q.val+(1-q.val)*x*(1-q.val)=1*x*1 at he
  simp only [one_mul,mul_one] at he
  have he' : q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=x-(t : ℂ) • q.val := by
    rw [show q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=
      (q.val*x*q.val+(1-q.val)*x*(1-q.val))-(t : ℂ) • q.val by abel,he]
  rw [he'] at hsum
  exact sub_nonneg.mp hsum

theorem positive_spectral_cut_ne_zero
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) (ht : 0 ≤ t) (htx : t < ‖x‖) :
    (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≠ 0 := by
  intro hz
  have h := cornerSpectralCut_upper ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  dsimp only at h
  rw [hz,sub_zero,one_mul,mul_one] at h
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_nonpos.mp h) hx
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg ht] at hn
  have hone := (IsStarProjection.one M.toStarSubalgebra).norm_le
  have hb : ‖x‖ ≤ t := hn.trans (by nlinarith)
  exact (not_lt_of_ge hb) htx

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_spectral_cut_lower
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    t*traceFreeDimension hfactor hdiff (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t) ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x t
  have hq : Commute q.val x := by
    show q.val*x=x*q.val
    simpa only [one_mul,mul_one] using cornerSpectralCut_commutes
      ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  have htq : Commute (t • q.val) x := by
    show (t • q.val)*x=x*(t • q.val)
    rw [smul_mul_assoc,mul_smul_comm,hq.eq]
  have hle : t • q.val ≤ x := by
    simpa only [Complex.coe_smul] using positive_spectral_cut_domination x hx t
  have h := dimensionSpectralValue_mono_of_commute hfactor hdiff hfinite hunit
    (t • q.val) x ((IsSelfAdjoint.all t).smul q.property.isSelfAdjoint) hx.isSelfAdjoint htq hle
  rw [dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit t q.val q.property.isSelfAdjoint,
    dimensionSpectralValue_projection hfactor hdiff hfinite hunit q,
    ← Complex.ofReal_mul,Complex.ofReal_re] at h
  exact h

theorem dimensionSpectralValue_pos
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hx0 : x≠0) :
    0 < (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x (‖x‖/2)
  have hq : q.val≠0 := positive_spectral_cut_ne_zero x hx (‖x‖/2) (by positivity) (by linarith)
  have hd : 0 < traceFreeDimension hfactor hdiff q := traceFreeDyadicSup_pos
    hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q hq
  exact (mul_pos (half_pos hn) hd).trans_le
    (dimensionSpectralValue_spectral_cut_lower hfactor hdiff hfinite hunit x hx (‖x‖/2))

theorem dimensionSpectralValue_eq_zero_iff_of_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint=0 ↔ x=0 := by
  constructor
  · intro h
    by_contra hx0
    have hp := dimensionSpectralValue_pos hfactor hdiff hfinite hunit x hx hx0
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  · intro h
    subst x
    exact dimensionSpectralValue_zero hfactor hdiff hfinite hunit

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology
section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_tendsto_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    Tendsto (fun i => traceFreeDimension hfactor hdiff (q i)) atTop
      (𝓝 (traceFreeDimension hfactor hdiff p)) := by
  rw [traceFreeDimension_isLUB_monotone hfactor hdiff hfinite hunit q hq p hp]
  exact tendsto_atTop_isLUB ((traceFreeDimension_mono hfactor hdiff).comp hq)
    (isLUB_csSup (Set.range_nonempty _) (traceFreeDimension_range_bddAbove hfactor hdiff q))

include hfinite in
/-- Concrete localization for a real linear combination of the actual vector
functional and the already constructed dimension; no linear trace is assumed. -/
theorem exists_signed_vector_dimension_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (c d : ℝ) (G : AlgebraProjection M) (hG : G.val≠0)
    (hμG : 0 ≤ c*G.vectorValue ξ+d*traceFreeDimension hfactor hdiff G) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧
      ∀ p, p ≤ F → 0 ≤ c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p := by
  apply AlgebraProjection.exists_nonnegative_corner
    (fun p => c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p) ?_ ?_ G hG hμG
  · intro p q ho
    have hν : (orthogonalSum p q ho).vectorValue ξ=p.vectorValue ξ+q.vectorValue ξ := by
      change (inner ℂ ξ (p.val.val ξ+q.val.val ξ)).re=_
      rw [inner_add_right,Complex.add_re]
      rfl
    have hD := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p q hunit (one_mul _) (one_mul _) ho
    change traceFreeDimension hfactor hdiff (orthogonalSum p q ho)=
      traceFreeDimension hfactor hdiff p+traceFreeDimension hfactor hdiff q at hD
    rw [hν,hD]
    ring
  · intro I _ _ _ a ha p hp
    exact ((AlgebraProjection.vectorValue_tendsto_monotone a ha p hp ξ).const_mul c).add
      ((traceFreeDimension_tendsto_monotone hfactor hdiff hfinite hunit a ha p hp).const_mul d)

include hfinite in
theorem exists_vector_dimension_lower_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      G.vectorValue ξ*traceFreeDimension hfactor hdiff p ≤
        p.vectorValue ξ*traceFreeDimension hfactor hdiff G := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (traceFreeDimension hfactor hdiff G) (-G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

include hfinite in
theorem exists_vector_dimension_upper_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      p.vectorValue ξ*traceFreeDimension hfactor hdiff G ≤
        G.vectorValue ξ*traceFreeDimension hfactor hdiff p := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (-traceFreeDimension hfactor hdiff G) (G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

end

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- An actual unit vector admits a nonzero corner on which every projection
value is between a D(p) and (1+ε)a D(p), with a strictly positive. -/
theorem exists_vector_dimension_localization
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ p : AlgebraProjection M, p ≤ E →
        a*traceFreeDimension hfactor hdiff p ≤ (inner ℂ ξ (p.val.val ξ)).re ∧
        (inner ℂ ξ (p.val.val ξ)).re ≤ (1+ε)*a*traceFreeDimension hfactor hdiff p := by
  classical
  let ν := AlgebraProjection.vectorValue (M := M) ξ
  let D := traceFreeDimension hfactor hdiff
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hν1 : ν oneP=1 := by
    change (inner ℂ ξ ξ).re=1
    rw [inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  have hD1 : D oneP=1 := traceFreeDyadicSup_self hfactor hdiff oneP
  have hDpos (p : AlgebraProjection M) (hp : p.val≠0) : 0<D p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite oneP p hp
  obtain ⟨F,_,hF,hlo⟩ := exists_vector_dimension_lower_corner
    hfactor hdiff hfinite hunit ξ oneP hunit
  have hFbound (p : AlgebraProjection M) (hp : p ≤ F) : D p ≤ ν p := by
    have hh := hlo p hp
    change ν oneP*D p ≤ ν p*D oneP at hh
    simpa only [hν1,hD1,one_mul,mul_one] using hh
  let R : Set ℝ := {b | ∃ p : AlgebraProjection M, p ≤ F ∧ p.val≠0 ∧ b=ν p/D p}
  have hRne : R.Nonempty := ⟨ν F/D F,F,le_rfl,hF,rfl⟩
  have hRlower : ∀ b ∈ R, 1 ≤ b := by
    rintro b ⟨p,hp,hpn,rfl⟩
    exact (le_div_iff₀ (hDpos p hpn)).mpr (by simpa only [one_mul] using hFbound p hp)
  have hRb : BddBelow R := ⟨1,hRlower⟩
  let a := sInf R
  have ha1 : 1 ≤ a := le_csInf hRne hRlower
  have ha : 0<a := lt_of_lt_of_le (by norm_num) ha1
  have hnear : a < (1+ε)*a := by nlinarith
  obtain ⟨_,⟨r,hrF,hr,hratio⟩,hnearR⟩ := exists_lt_of_csInf_lt hRne hnear
  rw [hratio] at hnearR
  obtain ⟨E,hEr,hE,hhi⟩ := exists_vector_dimension_upper_corner
    hfactor hdiff hfinite hunit ξ r hr
  refine ⟨E,a,hE,ha,?_⟩
  intro p hp
  by_cases hp0 : p.val=0
  · have hν0 : ν p=0 := by
      change (inner ℂ ξ (p.val.val ξ)).re=0
      rw [hp0]
      simp
    have hD0 : D p=0 := traceFreeDyadicSup_zero hfactor hdiff oneP p hunit hp0
    change a*D p ≤ ν p ∧ ν p ≤ (1+ε)*a*D p
    rw [hν0,hD0]
    simp
  · have hDp : 0<D p := hDpos p hp0
    have hpF : p ≤ F := hp.trans (hEr.trans hrF)
    have hap : a ≤ ν p/D p := csInf_le hRb ⟨p,hpF,hp0,rfl⟩
    have hloP : a*D p ≤ ν p := (le_div_iff₀ hDp).mp hap
    have hDr : 0<D r := hDpos r hr
    have hhiP := hhi p hp
    change ν p*D r ≤ ν r*D p at hhiP
    have hratioP : ν p ≤ (ν r/D r)*D p := by
      apply (mul_le_mul_iff_right₀ hDr).mp
      calc D r*ν p = ν p*D r := mul_comm _ _
           _ ≤ ν r*D p := hhiP
           _ = D r*(ν r/D r*D p) := by field_simp
    have hbound : (ν r/D r)*D p ≤ (1+ε)*a*D p :=
      mul_le_mul_of_nonneg_right hnearR.le hDp.le
    exact ⟨hloP,hratioP.trans hbound⟩

end

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.cornerValueCStar
attribute [local instance] OAI.Generator.Tracial.cornerValueOrder
local instance cornerValuePreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerValueLE
attribute [local instance] OAI.Generator.Tracial.cornerValueStarOrder
/-- A positive operator supported by p is approximated inside that same corner. -/
theorem exists_positive_corner_spectral_approximation
    (p : AlgebraProjection M) (x : M.toStarSubalgebra) (hx : 0 ≤ x)
    (hpx : p.val*x=x) (ε : ℝ) (hε : 0<ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧ (∀ i, Commute (Q.piece i).val x) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  have hxp : x*p.val=x := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hpx
  let I : SpectralInterval x :=
    { proj := p
      lo := 0
      hi := ‖x‖
      lower := by simpa only [hpx,hxp,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval p x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro i
    exact I.partition_commutes hx.isSelfAdjoint (Commute.refl x) (hpx.trans hxp.symm) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖p.val*x*p.val-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [hpx,hxp] using hn

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.corner_bound
    {x : M.toStarSubalgebra} {t : ℂ} (ht : IsDimensionSpectralValue hfactor hdiff x t)
    (p : AlgebraProjection M) (hpx : Commute p.val x)
    (Q : CornerPartition p) (c : Fin Q.size → ℂ) (hc : ∀ i, Commute (Q.piece i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (Q.piece i).val‖ := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let q : Fin Q.size ⊕ Unit → AlgebraProjection M := Sum.elim Q.piece (fun _ => r)
  let d : Fin Q.size ⊕ Unit → ℂ := Sum.elim c (fun _ => 0)
  have ho (i j : Fin Q.size ⊕ Unit) (h : i≠j) : (q i).val*(q j).val=0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact Q.orthogonal i j (fun he => h (congrArg Sum.inl he))
      | inr j =>
        change (Q.piece i).val*(1-p.val)=0
        rw [mul_sub,mul_one,projection_mul_of_le (Q.piece_le i),sub_self]
    | inr i =>
      cases j with
      | inl j =>
        change (1-p.val)*(Q.piece j).val=0
        rw [sub_mul,one_mul,show p.val*(Q.piece j).val=(Q.piece j).val from Q.piece_le j,sub_self]
      | inr j => exact (h (congrArg Sum.inr (Subsingleton.elim i j))).elim
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    simp only [q,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,Q.total]
    change p.val+(1-p.val)=1
    abel
  have hqc (i : Fin Q.size ⊕ Unit) : Commute (q i).val x := by
    cases i with
    | inl i => exact hc i
    | inr i => exact (Commute.one_left x).sub_left hpx
  have hh := ht.family_bound hfactor hdiff q ho hs d hqc
  simpa only [q,d,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,zero_mul,zero_smul,
    Finset.sum_const_zero,add_zero] using hh

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.localizedCStar
attribute [local instance] OAI.Generator.Tracial.localizedOrder
local instance localizedPreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.localizedLE
attribute [local instance] OAI.Generator.Tracial.localizedStarOrder
theorem positive_functional_bounds_of_projection_bounds
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (E : AlgebraProjection M)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hproj : ∀ p : AlgebraProjection M, p ≤ E →
      a*traceFreeDimension hfactor hdiff p ≤ (φ p.val).re ∧
      (φ p.val).re ≤ b*traceFreeDimension hfactor hdiff p)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hEx : E.val*x=x) :
    a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤ (φ x).re ∧
      (φ x).re ≤ b*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  have hxE : x*E.val=x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hEx
  have happrox (ε : ℝ) (hε : 0<ε) :
      a*t.re ≤ (φ x).re+ε ∧ (φ x).re ≤ b*t.re+ε := by
    let C := a+b+‖φ‖+1
    have hC : 0<C := by dsimp [C]; positivity
    let δ := ε/C
    have hδ : 0<δ := div_pos hε hC
    have hCδ : C*δ=ε := mul_div_cancel₀ _ hC.ne'
    obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_corner_spectral_approximation E x hx hEx δ hδ
    let y : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
    let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
    let v : ℝ := (φ y).re
    have hw : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
      simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
    have hv : v=∑ i, c i*(φ (Q.piece i).val).re := by
      simp only [v,y,map_sum,map_smul,smul_eq_mul,Complex.re_sum,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hav : a*w ≤ v := by
      rw [hv,show a*w=∑ i, c i*(a*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).1 (hc i))
    have hvb : v ≤ b*w := by
      rw [hv,show b*w=∑ i, c i*(b*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).2 (hc i))
    have hspec := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2.corner_bound
      hfactor hdiff E (hEx.trans hxE.symm) Q (fun i => (c i : ℂ)) hQ
    have htw : |t.re-w| ≤ δ := by
      have h := Complex.abs_re_le_norm (t-(w : ℂ))
      rw [Complex.sub_re,Complex.ofReal_re] at h
      apply h.trans
      rw [hw]
      exact hspec.trans herr.le
    have hφ : |(φ x).re-v| ≤ ‖φ‖*δ := by
      have he : (φ x).re-v=(φ (x-y)).re := by rw [map_sub,Complex.sub_re]
      rw [he]
      exact (Complex.abs_re_le_norm _).trans ((φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left herr.le (norm_nonneg φ)))
    have htw' := abs_le.mp htw
    have hφ' := abs_le.mp hφ
    have had := mul_nonneg ha hδ.le
    have hbd := mul_nonneg hb hδ.le
    dsimp only [C] at hCδ
    constructor <;> nlinarith
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).1
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).2

/-- Concrete projection and positive-operator localization, with an actual
bounded complex-linear functional and a nonzero constructed corner. -/
theorem exists_localized_vector_functional
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ (x : M.toStarSubalgebra) (hx : 0 ≤ x), E.val*x=x →
        a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤
          (vectorFunctional ξ x).re ∧
        (vectorFunctional ξ x).re ≤
          (1+ε)*a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  obtain ⟨E,a,hE,ha,hp⟩ := exists_vector_dimension_localization hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,a,hE,ha,?_⟩
  intro x hx hEx
  exact positive_functional_bounds_of_projection_bounds hfactor hdiff hfinite hunit
    (vectorFunctional ξ) E a ((1+ε)*a) ha.le (mul_nonneg (by linarith) ha.le) hp x hx hEx

end

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.cornerStateCStar
attribute [local instance] OAI.Generator.Tracial.cornerStateOrder
local instance cornerStatePreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.cornerStateLE
attribute [local instance] OAI.Generator.Tracial.cornerStateStarOrder
include hfactor hdiff hfinite in
/-- A localized vector functional is nearly cyclic for every element in its
corner. This gives both inequalities by applying the result to x and x*. -/
theorem exists_corner_nearly_cyclic_vector
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ E : AlgebraProjection M, E.val≠0 ∧
      (∀ p : AlgebraProjection M, p ≤ E → p.val≠0 → 0<(vectorFunctional ξ p.val).re) ∧
      ∀ x : M.toStarSubalgebra, E.val*x=x → x*E.val=x →
        (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re := by
  obtain ⟨E,a,hE,ha,h⟩ := exists_localized_vector_functional
    hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,hE,?_,?_⟩
  · intro p hp hpn
    have hpstar : star p.val*p.val=p.val := by
      rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
    have hpnonneg : 0 ≤ p.val := hpstar ▸ star_mul_self_nonneg p.val
    have hh := (h p.val hpnonneg hp).1
    rw [dimensionSpectralValue_projection,Complex.ofReal_re] at hh
    exact (mul_pos ha (traceFreeDyadicSup_pos hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hpn)).trans_le hh
  intro x hEx hxE
  have hExs : E.val*star x=star x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq] using congrArg star hxE
  have h₁ := h (star x*x) (star_mul_self_nonneg x) (by rw [← mul_assoc,hExs])
  have h₂ := h (x*star x) (mul_star_self_nonneg x) (by rw [← mul_assoc,hEx])
  have he := congrArg Complex.re (dimensionSpectralValue_star_mul_self hfactor hdiff hfinite hunit x)
  have hm := mul_le_mul_of_nonneg_left h₂.1 (by linarith : 0 ≤ 1+ε)
  rw [← he] at hm
  nlinarith [h₁.2]

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- Every actual finite equivalent partition has the expected base dimension. -/
theorem EquivalentPartition.dimension_base
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {p : AlgebraProjection M} {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : EquivalentPartition p ι) :
    traceFreeDimension hfactor hdiff E.base=traceFreeDimension hfactor hdiff p/Fintype.card ι := by
  have he (i : ι) : traceFreeDimension hfactor hdiff (E.leg i).target=
      traceFreeDimension hfactor hdiff E.base :=
    (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show E.base.Equivalent (E.leg i).target from ⟨E.leg i,E.initial i,rfl⟩)).symm
  have h := traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => (E.leg i).target) E.orthogonal p E.total
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  apply (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card ι : ℝ)≠0)).mpr
  linarith

include hfactor hdiff hfinite in
/-- A partition of 1 with common initial projection inside any given nonzero E. -/
theorem exists_equivalent_partition_base_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (E : AlgebraProjection M) (hE : E.val≠0) :
    ∃ (n : ℕ) (_hn : 0<n)
      (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) (Fin n)),
      Q.base ≤ E ∧ Q.base.val≠0 := by
  have hD : 0<traceFreeDimension hfactor hdiff E :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ E hE
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hD (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : 0<2^n := Nat.two_pow_pos n
  let Q := Classical.choice (traceFreeDimension_exists_equivalent_partition
    hfactor hdiff hfinite hunit (2^n) hn0 ⟨1,IsStarProjection.one _⟩)
  have : Nonempty (Fin (2^n)) := ⟨⟨0,hn0⟩⟩
  have hQ : traceFreeDimension hfactor hdiff Q.base=1/2^n := by
    rw [Q.dimension_base hfactor hdiff hfinite hunit]
    have h1 : traceFreeDimension hfactor hdiff (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M)=1 :=
      traceFreeDyadicSup_self hfactor hdiff ⟨1,IsStarProjection.one _⟩
    rw [h1]
    simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit Q.base E).mp
    (by rw [hQ]; exact hn.le)
  have hvt : v.adjoint.target=Q.base := by
    apply Subtype.ext
    change star v.val*star (star v.val)=Q.base.val
    rw [star_star,v.initial,hv]
  let R := Q.rebase v.adjoint hvt
  exact ⟨2^n,hn0,R,ht,R.base_ne_zero hunit⟩

end

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.approxTraceCStar
local instance approxTraceOrder_rd5365d_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approxTracePreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.approxTraceLE
local instance approxTraceStarOrder_rd5365d_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
include hfactor hdiff hfinite in
/-- A constructed approximate tracial state on the entire original algebra. -/
theorem exists_approximately_tracial_state
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (ε : ℝ) (hε : 0<ε) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re ≤ (1+ε)*(φ (x*star x)).re := by
  classical
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,hE,hfaith,hcorner⟩ := exists_corner_nearly_cyclic_vector
    hfactor hdiff hfinite hunit ξ hξ ε hε
  obtain ⟨n,hn,Q,hQE,hQ⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  have hbase : 0<(vectorFunctional ξ Q.base.val).re := hfaith Q.base hQE hQ
  let A : ℝ := ∑ i, ‖(Q.leg i).val.val ξ‖^2
  have hi (i : Fin n) : ‖(Q.leg i).val.val ξ‖^2=(vectorFunctional ξ Q.base.val).re := by
    have h := congrArg Complex.re (vectorFunctional_star_mul_self ξ (Q.leg i).val)
    rw [(Q.leg i).initial,Q.initial] at h
    exact_mod_cast h.symm
  have hA : 0<A := by
    apply Finset.sum_pos
    · intro i _
      rw [hi]
      exact hbase
    · exact ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  let F := Q.matrixVectorFunctional ξ
  have hF1 : F 1=(A : ℂ) := Q.matrixVectorFunctional_one ξ
  have hFnorm : ‖F‖ ≤ A := Q.matrixVectorFunctional_norm_le ξ
  have hFpos (x : M.toStarSubalgebra) (hx : 0 ≤ x) : 0 ≤ (F x).re := by
    change 0 ≤ ((∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x).re
    rw [sum_apply,Complex.re_sum]
    exact Finset.sum_nonneg (fun i _ => vectorFunctional_positive _ x hx)
  have hFtrace (x : M.toStarSubalgebra) : (F (star x*x)).re ≤ (1+ε)*(F (x*star x)).re := by
    apply Q.matrixVectorFunctional_nearly_cyclic rfl ξ ε ?_ x
    intro y hly hry
    have hl : E.val*y=y := by
      calc E.val*y = E.val*(Q.base.val*y) := by rw [hly]
           _ = y := by rw [← mul_assoc,show E.val*Q.base.val=Q.base.val from hQE,hly]
    have hr : y*E.val=y := by
      calc y*E.val = (y*Q.base.val)*E.val := by rw [hry]
           _ = y := by rw [mul_assoc,projection_mul_of_le hQE,hry]
    exact hcorner y hl hr
  let φ : M.toStarSubalgebra →L[ℂ] ℂ := ((A⁻¹ : ℝ) : ℂ) • F
  have hφ (x : M.toStarSubalgebra) : (φ x).re=A⁻¹*(F x).re := by
    simp only [φ,smul_apply,smul_eq_mul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨φ,?_,?_,?_,?_⟩
  · change ‖((A⁻¹ : ℝ) : ℂ) • F‖ ≤ 1
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hA.le)]
    exact (mul_le_mul_of_nonneg_left hFnorm (inv_nonneg.mpr hA.le)).trans_eq (inv_mul_cancel₀ hA.ne')
  · change ((A⁻¹ : ℝ) : ℂ)*(F 1)=1
    rw [hF1,← Complex.ofReal_mul,inv_mul_cancel₀ hA.ne',Complex.ofReal_one]
  · intro x hx
    rw [hφ]
    exact mul_nonneg (inv_nonneg.mpr hA.le) (hFpos x hx)
  · intro x
    rw [hφ,hφ]
    have h := mul_le_mul_of_nonneg_left (hFtrace x) (inv_nonneg.mpr hA.le)
    calc A⁻¹*(F (star x*x)).re ≤ A⁻¹*((1+ε)*(F (x*star x)).re) := h
         _ = (1+ε)*(A⁻¹*(F (x*star x)).re) := by ring

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.quadraticStateCStar
local instance quadraticStateOrder_rd5365d_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance quadraticStatePreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.quadraticStateLE
local instance quadraticStateStarOrder_rd5365d_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
include hfactor hdiff hfinite in
theorem exists_real_quadratic_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re=(φ (x*star x)).re := by
  have hex (n : ℕ) := exists_approximately_tracial_state hfactor hdiff hfinite hunit
    (1/((n : ℝ)+1)) (by positivity)
  choose f hf hfone hfpos hfquad using hex
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨φ,hφ,ht⟩ := exists_bounded_functional_ultralimit ω f 1 (by norm_num) hf
  have hε : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  have hre (x : M.toStarSubalgebra) := (Complex.continuous_re.tendsto (φ x)).comp (ht x)
  have hle (x : M.toStarSubalgebra) : (φ (star x*x)).re ≤ (φ (x*star x)).re := by
    have hr := (hε.const_add 1).mul (hre (x*star x))
    have h := le_of_tendsto_of_tendsto (hre (star x*x)) hr
      (Eventually.of_forall (fun n => hfquad n x))
    simpa only [add_zero,one_mul] using h
  refine ⟨φ,hφ,?_,?_,?_⟩
  · apply tendsto_nhds_unique (ht 1)
    simpa only [hfone] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) (ω : Filter ℕ) (𝓝 1))
  · intro x hx
    exact ge_of_tendsto (hre x) (Eventually.of_forall (fun n => hfpos n x hx))
  · intro x
    exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

end

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.tracialStateCStar
attribute [local instance] OAI.Generator.Tracial.tracialStateOrder
local instance tracialStatePreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.tracialStateLE
attribute [local instance] OAI.Generator.Tracial.tracialStateStarOrder
include hfactor hdiff hfinite in
theorem exists_tracial_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      (∀ x : M.toStarSubalgebra, φ (star x)=star (φ x)) ∧
      ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x) := by
  obtain ⟨φ,hφ,h1,hpos,hquad⟩ := exists_real_quadratic_state hfactor hdiff hfinite hunit
  refine ⟨hermitianFunctional φ,(hermitianFunctional_norm_le φ).trans hφ,
    hermitianFunctional_one φ h1,?_,hermitianFunctional_star φ,
    hermitianFunctional_trace φ hquad⟩
  intro x hx
  rw [hermitianFunctional_selfAdjoint φ x hx.isSelfAdjoint,Complex.ofReal_re]
  exact hpos x hx

end

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralAdditivityCStar
local instance spectralAdditivityOrder_rd5365d_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralAdditivityPreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralAdditivityLE_rd5365d_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralAdditivityStarOrder_rd5365d_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem functional_eq_dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    φ x=dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  (functional_isDimensionSpectralValue hfactor hdiff φ hnorm hproj x).unique hfactor hdiff hx
    (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceCStar
attribute [local instance] OAI.Generator.Tracial.traceOrder
local instance tracePreorder_rd5365d_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.traceLE
attribute [local instance] OAI.Generator.Tracial.traceStarOrder
def traceFreeTrace : M.toStarSubalgebra →L[ℂ] ℂ :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose

theorem traceFreeTrace_spec :
    ‖traceFreeTrace hfactor hdiff hfinite hunit‖ ≤ 1 ∧
    traceFreeTrace hfactor hdiff hfinite hunit 1=1 ∧
    (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (traceFreeTrace hfactor hdiff hfinite hunit x).re) ∧
    (∀ x : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (star x)=
      star (traceFreeTrace hfactor hdiff hfinite hunit x)) ∧
    ∀ x y : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (x*y)=
      traceFreeTrace hfactor hdiff hfinite hunit (y*x) :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose_spec

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end


