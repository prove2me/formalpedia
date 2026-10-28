-- Prove2me | Definitions.Def_OAIQ66So026
-- name    : OAIQ66So026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:32:02.811604+00:00
-- url     : https://prove2.me/theorems/3035e7f5-11b5-4bec-92aa-619c1767f9ba
-- title:
--   Definitions bundle OAIQ66So026 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 106 declarations of OpenAI's Lean: 42 definitions, 1 inductive type or structure, 4 instances and 59 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticProduct.evaluation`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticProduct.normal`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticProduct.pairEval`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticProduct.value`, `OAI.SimpleFInftyOvergroups.SplittingTorusModel`, `OAI.SimpleFInftyOvergroups.SplittingTorusModel.relabel`, `OAI.SourceEnlargement.Double.ambientDiagrams₂`, `OAI.SourceEnlargement.Double.ambientDiagrams₃`, `OAI.SourceEnlargement.Double.diagrams₂`, `OAI.SourceEnlargement.Double.diagrams₃`, `OAI.SourceEnlargement.Double.iota`, `OAI.SourceEnlargement.Double.point`, `OAI.SourceEnlargement.pairDiagrams`, `OAI.SteinChains.Complex.faceModule`, `OAI.SteinChains.Descending`, `OAI.SteinChains.faceCarrier`, `OAI.SteinChains.select`, `OAI.TorusStabilizer.torusEquiv`, `OAI.TwistedBrin.Basis.CutInterval.core`, `OAI.TwistedBrin.Basis.CutSelections.Proper`, `OAI.TwistedBrin.Basis.CutSelections.ofInterval`, `OAI.TwistedBrin.Basis.CutSelections.properBooleanBoundary`, `OAI.TwistedBrin.Basis.CutSelections.toInterval`, `OAI.TwistedBrin.Basis.Merge.Roots`, `OAI.TwistedBrin.Basis.Merge.leafEquiv`, `OAI.TwistedBrin.Basis.Merge.lower`, `OAI.TwistedBrin.Basis.Merge.ofPair`, `OAI.TwistedBrin.Basis.Merge.rootChart`, `OAI.TwistedBrin.Basis.descendants`, `OAI.TwistedBrin.Basis.groundMatching`, `OAI.TwistedBrin.Basis.intervalCode`, `OAI.TwistedBrin.Basis.rankModel`, `OAI.TwistedBrin.Basis.twistPiecesToKernel`, `OAI.TwistedBrin.Basis.twistPiecesToVertex`, `OAI.TwistedBrin.Basis.vertexKernelEquiv`, `OAI.TwistedBrin.BrickSwap.fn`, `OAI.TwistedBrin.Localization.gridIndex`, `OAI.TwistedBrin.Localization.hom`, `OAI.TwistedBrin.PartitionMaps.equiv`, `OAI.TwistedBrin.PartitionMaps.pieces` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_AscendingHNNInnerTwist`, `FiniteType_HomStabilizer`, `FiniteType_NonunitalCompression`, `FiniteType_OrderChainsExactSubtypeOfExactSet`, `FiniteType_OrderListChainsBased`, `FiniteType_RingExchange`, `FiniteType_SteinbergSixThree`, `FiniteType_TwistedBrin`, `FiniteType_TwistedBrinBasis`, `FiniteType_TwistedBrinBasisFirstCut`, `FiniteType_TwistedBrinBasisGroundMatching`, `FiniteType_TwistedBrinBasisTranslateEquiv`, `FiniteType_TwistedBrinEquiv`, `FiniteType_TwistedBrinGermBrick`, `FiniteType_TwistedBrinPatternFactor`, `FiniteType_TwistedBrinRangeChartRestricts`, `SimpleOvergroups_SemanticProduct`, `SimpleOvergroups_TwoEnlargements`.
--
--   **Imports.** It imports the bundles `OAIQ66So018`, `OAIQ66So019`, `OAIQ66So020`, `OAIQ66So021` and `OAIQ66So022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So027`, `OAIQ66So028` and `OAIQ66So029`; the statement `OAI.SimpleFInftyOvergroups.SplittingTorusModel.products`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So018
import Definitions.Def_OAIQ66So019
import Definitions.Def_OAIQ66So020
import Definitions.Def_OAIQ66So021
import Definitions.Def_OAIQ66So022

section
-- module Solutions.OAIQ066_SO.FiniteType_NonunitalCompression
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg

variable {n m R : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma kernel_commute_column (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (v : n → Multiplicative R) :
    Commute (reindex f z) (column f k hk v) := by
  have hm : matrix z = 1 := congrArg Subtype.val hz
  have h := conjugate_column f k hk z v
  rw [hm] at h
  simp only [Units.val_one, matrixVector_one] at h
  change reindex f z * column f k hk v = column f k hk v * reindex f z
  calc
    _ = (reindex f z * column f k hk v * (reindex f z)⁻¹) * reindex f z := by group
    _ = _ := by rw [h]

lemma kernel_commute_outside_root (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (i : n) (a : R) :
    Commute (reindex f z) (root (f i) k (hk i) a) := by
  have h := kernel_commute_column f k hk z hz (Pi.mulSingle i (Multiplicative.ofAdd a))
  rwa [column_single] at h

lemma kernel_commute_row (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (v : n → Multiplicative R) :
    Commute (reindex f z) (row f k hk v) := by
  have hm : matrix z = 1 := congrArg Subtype.val hz
  have h := conjugate_row f k hk z v
  rw [hm] at h
  simp only [inv_one, Units.val_one, vectorMatrix_one] at h
  change reindex f z * row f k hk v = row f k hk v * reindex f z
  calc
    _ = (reindex f z * row f k hk v * (reindex f z)⁻¹) * reindex f z := by group
    _ = _ := by rw [h]

lemma kernel_commute_outside_row_root (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (i : n) (a : R) :
    Commute (reindex f z) (root k (f i) (Ne.symm (hk i)) a) := by
  have h := kernel_commute_row f k hk z hz (Pi.mulSingle i (Multiplicative.ofAdd a))
  rwa [row_single] at h

lemma reindex_kernel_central (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (z : Group n R) (hz : pi z = 1) (w : Group m R) :
    Commute (reindex f z) w := by
  classical
  suffices hs : ∀ i j hij a, Commute (root i j hij a) (reindex f z) from
    (commute_of_roots (MonoidHom.id (Group m R)) (reindex f z) hs w).symm
  intro i j hij a
  by_cases hi : ∃ p, f p = i
  · obtain ⟨p, rfl⟩ := hi
    by_cases hj : ∃ q, f q = j
    · obtain ⟨q, rfl⟩ := hj
      have hc := kernel_commute_outside_root f k hk z hz p a
      have hr := kernel_commute_outside_row_root f k hk z hz q (1:R)
      have h := ((hc.mul_right hr).mul_right hc.inv_right).mul_right hr.inv_right
      rw [← commutatorElement_def, root_commutator (f p) k (f q)
        (hk p) (Ne.symm (hk q)) hij, mul_one] at h
      exact h.symm
    · have hj' : ∀ p, f p ≠ j := by simpa only [not_exists] using hj
      exact (kernel_commute_outside_root f j hj' z hz p a).symm
  · have hi' : ∀ p, f p ≠ i := by simpa only [not_exists] using hi
    by_cases hj : ∃ q, f q = j
    · obtain ⟨q, rfl⟩ := hj
      exact (kernel_commute_outside_row_root f i hi' z hz q a).symm
    · have hj' : ∀ p, f p ≠ j := by simpa only [not_exists] using hj
      apply Commute.symm
      apply commute_of_roots (reindex f) (root i j hij a) _ z
      intro p q hpq b
      simp only [reindex_root]
      exact root_commute (f p) (f q) i j (f.injective.ne hpq) hij (hj' p) (hi' q) b a

variable [Fintype m] [DecidableEq m]

lemma supported_kernel_central (A : Set m) (k : m) (hk : k ∉ A)
    (z : Group m R) (hmem : z ∈ supported A) (hz : pi z = 1) (w : Group m R) :
    Commute z w := by
  classical
  obtain ⟨v, rfl⟩ := hmem
  exact reindex_kernel_central (Function.Embedding.subtype _) k
    (by intro i he; exact hk (he ▸ i.property)) v
    (kernel_of_reindex _ v hz) w

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
lemma column_mem_supported (A : Set m) (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (v : n → Multiplicative R) (hA : k ∈ A) (hv : ∀ i, f i ∉ A → (v i).toAdd = 0) :
    column f k hk v ∈ supported A := by
  refine (supported A).noncommProd_mem
    (by intro i _ j _ _; exact columnRoot_commute f k hk i j _ _) ?_
  intro i _
  by_cases hi : f i ∈ A
  · exact root_mem_supported A (f i) k (hk i) _ hi hA
  · change root (f i) k (hk i) ((v i).toAdd) ∈ _
    rw [hv i hi, root_zero]
    exact (supported A).one_mem

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
lemma row_mem_supported (A : Set m) (f : n ↪ m) (k : m) (hk : ∀ i, f i ≠ k)
    (v : n → Multiplicative R) (hA : k ∈ A) (hv : ∀ i, f i ∉ A → (v i).toAdd = 0) :
    row f k hk v ∈ supported A := by
  refine (supported A).noncommProd_mem
    (by intro i _ j _ _; exact rowRoot_commute f k hk i j _ _) ?_
  intro i _
  by_cases hi : f i ∈ A
  · exact root_mem_supported A k (f i) (Ne.symm (hk i)) _ hA hi
  · change root k (f i) (Ne.symm (hk i)) ((v i).toAdd) ∈ _
    rw [hv i hi, root_zero]
    exact (supported A).one_mem

omit [Fintype m] [DecidableEq m] in
lemma conjugate_column_root_mem_supported (A : Set m) (f : n ↪ m) (z : Group n R)
    (k : m) (hk : ∀ i, f i ≠ k) (hA : k ∈ A) (j : n) (a : R)
    (hcol : ∀ i, f i ∉ A → (matrix z).val i j*a=0) :
    reindex f z * root (f j) k (hk j) a * (reindex f z)⁻¹ ∈ supported A := by
  have h := conjugate_column f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  rw [column_single] at h
  change reindex f z * root (f j) k (hk j) a * (reindex f z)⁻¹ = _ at h
  rw [h]
  apply column_mem_supported A f k hk _ hA
  intro i hi
  rw [matrixVector_single_apply]
  exact hcol i hi

omit [Fintype m] [DecidableEq m] in
lemma conjugate_row_root_mem_supported (A : Set m) (f : n ↪ m) (z : Group n R)
    (k : m) (hk : ∀ i, f i ≠ k) (hA : k ∈ A) (j : n) (a : R)
    (hrow : ∀ i, f i ∉ A → a*((matrix z)⁻¹).val j i=0) :
    reindex f z * root k (f j) (Ne.symm (hk j)) a * (reindex f z)⁻¹ ∈ supported A := by
  have h := conjugate_row f k hk z (Pi.mulSingle j (Multiplicative.ofAdd a))
  rw [row_single] at h
  change reindex f z * root k (f j) (Ne.symm (hk j)) a * (reindex f z)⁻¹ = _ at h
  rw [h]
  apply row_mem_supported A f k hk _ hA
  intro i hi
  rw [vectorMatrix_single_apply]
  exact hrow i hi

omit [Fintype m] in

lemma conjugate_coefficient_supported (A : Set m) (f : n ↪ m) (z : Group n R)
    (t : m) (ht : ∀ i, f i ≠ t) (η : R →ₙ+* R)
    (houtside : ∀ k, (∀ i, f i ≠ k) → k ∈ A)
    (hcol : ∀ i, f i ∉ A → ∀ j a, (matrix z).val i j * η a=0)
    (hrow : ∀ i, f i ∉ A → ∀ j a, η a * ((matrix z)⁻¹).val j i=0)
    (w : Group m R) :
    reindex f z * map η w * (reindex f z)⁻¹ ∈ supported A := by
  let C : Group m R →* Group m R := (MulAut.conj (reindex f z)).toMonoidHom
  have hroots : ∀ p q hpq a, C (root p q hpq (η a)) ∈ supported A := by
    intro p q hpq a
    by_cases hp : ∃ i, f i = p
    · obtain ⟨i, rfl⟩ := hp
      by_cases hq : ∃ j, f j = q
      · obtain ⟨j, rfl⟩ := hq
        have he : root (f i) (f j) hpq (η a) =
            ⁅root (f i) t (ht i) (η a), root t (f j) (Ne.symm (ht j)) (η 1)⁆ := by
          rw [root_commutator _ _ _ (ht i) (Ne.symm (ht j)) hpq, ← map_mul, mul_one]
        rw [he, map_commutatorElement]
        have h₁ : C (root (f i) t (ht i) (η a)) ∈ supported A :=
          conjugate_column_root_mem_supported A f z t ht (houtside t ht) i (η a)
            (fun k hk => hcol k hk i a)
        have h₂ : C (root t (f j) (Ne.symm (ht j)) (η 1)) ∈ supported A :=
          conjugate_row_root_mem_supported A f z t ht (houtside t ht) j (η 1)
            (fun k hk => hrow k hk j 1)
        exact (supported A).mul_mem
          ((supported A).mul_mem ((supported A).mul_mem h₁ h₂) ((supported A).inv_mem h₁))
          ((supported A).inv_mem h₂)
      · have hq' : ∀ j, f j ≠ q := by simpa only [not_exists] using hq
        exact conjugate_column_root_mem_supported A f z q hq' (houtside q hq') i (η a)
          (fun k hk => hcol k hk i a)
    · have hp' : ∀ i, f i ≠ p := by simpa only [not_exists] using hp
      by_cases hq : ∃ j, f j = q
      · obtain ⟨j, rfl⟩ := hq
        exact conjugate_row_root_mem_supported A f z p hp' (houtside p hp') j (η a)
          (fun k hk => hrow k hk j a)
      · have hq' : ∀ j, f j ≠ q := by simpa only [not_exists] using hq
        change reindex f z * root p q hpq (η a) * (reindex f z)⁻¹ ∈ _
        rw [(reindex_commute_disjoint f p q hpq hp' hq' z (η a)).mul_inv_cancel]
        exact root_mem_supported A p q hpq (η a) (houtside p hp') (houtside q hq')
  have hw : w ∈ (supported A).comap (C.comp (map η)) := by
    apply PresentedGroup.generated_by
    intro r
    change C (map η (root r.i r.j r.different r.coefficient)) ∈ supported A
    rw [map_root]
    exact hroots r.i r.j r.different r.coefficient
  exact hw

lemma localized_coefficient_kernel_central (A : Set m) (f : n ↪ m) (z : Group n R)
    (t : m) (ht : ∀ i, f i ≠ t) (η : R →ₙ+* R)
    (houtside : ∀ k, (∀ i, f i ≠ k) → k ∈ A)
    (hcol : ∀ i, f i ∉ A → ∀ j a, (matrix z).val i j * η a=0)
    (hrow : ∀ i, f i ∉ A → ∀ j a, η a * ((matrix z)⁻¹).val j i=0)
    (b : m) (hb : b ∉ A) (w : Group m R) (hw : pi w=1) (v : Group m R) :
    Commute (map η w) v := by
  let c := reindex f z * map η w * (reindex f z)⁻¹
  have hmem : c ∈ supported A :=
    conjugate_coefficient_supported A f z t ht η houtside hcol hrow w
  have hc : pi c=1 := by
    simp [c, map_preserves_kernel η w hw]
  have hcentral : ∀ v, Commute c v := supported_kernel_central A b hb c hmem hc
  have he : map η w = c := by
    calc
      map η w = (reindex f z)⁻¹ * c * ((reindex f z)⁻¹)⁻¹ := by dsimp [c]; group
      _ = c := (hcentral (reindex f z)).symm.inv_left.mul_inv_cancel
  rw [he]
  exact hcentral v

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RingExchange
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
section
variable {R : Type*} [Ring R]

lemma flip_kernel_central (D : RingExchange.Data R) (η : R →ₙ+* R)
    (hleft : ∀ x, D.E*η x=η x) (hright : ∀ x, η x*D.E=η x)
    (w : Group SixIndices R) (hw : pi w=1) (v : Group SixIndices R) :
    Commute (map η w) v := by
  let z := blockBalanced D.flipUnit
  let f : (Fin 2 ⊕ Fin 2) ↪ SixIndices := Function.Embedding.inl
  have hz : (matrix z).val = Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix :=
    matrix_blockBalanced D.flipUnit
  have hi : ((matrix z)⁻¹).val = Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix := by
    have hs : (Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
        Matrix.fromBlocks D.flipMatrix 0 0 D.flipMatrix = 1 := by
      simp [Matrix.fromBlocks_multiply,D.flipMatrix_square,Matrix.fromBlocks_one]
    have he : (matrix z) * (matrix z) = 1 := Units.ext (by simpa only [Units.val_mul,Units.val_one,hz] using hs)
    exact (congrArg Units.val (inv_eq_of_mul_eq_one_left he)).trans hz
  apply localized_coefficient_kernel_central retainedIndices f z (Sum.inr 0)
    (by intro i; simp [f]) η ?_ ?_ ?_ (Sum.inl (Sum.inl 1)) (by change (1 : Fin 2) ≠ 0; decide) w hw v
  · intro k hk
    cases k with
    | inl a => exact False.elim (hk a rfl)
    | inr a => trivial
  · intro i hiA j a
    rw [hz]
    cases i with
    | inl i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => exact D.flip_bad_row η hleft a j
      | inr j => simp
    | inr i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => simp
      | inr j => exact D.flip_bad_row η hleft a j
  · intro i hiA j a
    rw [hi]
    cases i with
    | inl i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => exact D.flip_bad_col η hright a j
      | inr j => simp
    | inr i =>
      have hi0 : i ≠ 0 := hiA
      have hi1 : i=1 := by fin_cases i <;> simp_all
      subst i
      cases j with
      | inl j => simp
      | inr j => exact D.flip_bad_col η hright a j

end

variable {R m : Type*} [Ring R]

lemma scalar_involution_inner (u : Rˣ) (hu : u.inv=u.val) :
    ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (fun _ => u) := by
  have h₀ : ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (scalarWeight₀ u) := by
    let f : Fin 2 ↪ SixIndices := Function.Embedding.inl.trans Function.Embedding.inl
    apply constantPair_inner u hu f (scalarWeight₀ u) (by intro i; rfl)
      (Sum.inr 0) (by intro i; simp [f])
    intro j hj
    rcases j with (j|j)|j
    · exact False.elim (hj j rfl)
    · rfl
    · rfl
  have h₁ : ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (scalarWeight₁ u) := by
    let f : Fin 2 ↪ SixIndices := Function.Embedding.inr.trans Function.Embedding.inl
    apply constantPair_inner u hu f (scalarWeight₁ u) (by intro i; rfl)
      (Sum.inr 0) (by intro i; simp [f])
    intro j hj
    rcases j with (j|j)|j
    · rfl
    · exact False.elim (hj j rfl)
    · rfl
  have h₂ : ∃ z : Group SixIndices R,
      (MulAut.conj z).toMonoidHom=diagonalAction (scalarWeight₂ u) := by
    let f : Fin 2 ↪ SixIndices := Function.Embedding.inr
    apply constantPair_inner u hu f (scalarWeight₂ u) (by intro i; rfl)
      (Sum.inl (Sum.inl 0)) (by intro i; simp [f])
    intro j hj
    cases j with
    | inl j => rfl
    | inr j => exact False.elim (hj j rfl)
  have h := innerWeights_mul _ _ (innerWeights_mul _ _ h₀ h₁) h₂
  rwa [scalarWeight_product] at h

lemma central_conjugated_coefficients (u : Rˣ) (hu : u.inv=u.val)
    (η θ : R →ₙ+* R) (hη : ∀ a, θ a=u.val*η a*u.inv)
    (w : Group SixIndices R) (hc : ∀ v : Group SixIndices R, Commute (map η w) v) :
    map θ w=map η w := by
  obtain ⟨z,hz⟩ := scalar_involution_inner u hu
  have he : map θ = (diagonalAction (fun _ : SixIndices => u)).comp (map η) := by
    apply hom_ext
    intro i j hij a
    simp [hη]
  rw [he,← hz]
  change z * map η w * z⁻¹=map η w
  exact (hc z).symm.mul_inv_cancel

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace Steinberg
section
variable {R : Type*} [Ring R]

lemma exchange_coefficient_kernel_central {φ : R →ₙ+* R}
    (E : CompressedSplittings.Idempotent φ) (D : RingExchange.Data R) (hD : D.E=E.val)
    (w : Group SixIndices R) (hw : pi w=1) (v : Group SixIndices R) :
    Commute (map E.coefficient w) v :=
  flip_kernel_central D E.coefficient (by simpa [hD] using E.coefficient_left)
    (by simpa [hD] using E.coefficient_right) w hw v

lemma exchange_coefficient_kernel_equal {φ : R →ₙ+* R}
    (E F : CompressedSplittings.Idempotent φ) (D : RingExchange.Data R)
    (hE : D.E=E.val) (hF : D.F=F.val)
    (hc : ∀ a, Commute D.unit.val (φ a))
    (w : Group SixIndices R) (hw : pi w=1) : map E.coefficient w=map F.coefficient w := by
  apply Eq.symm
  apply central_conjugated_coefficients D.unit (by rfl) E.coefficient F.coefficient
  · exact E.coefficient_conjugate F D.unit hc (by simpa [hE,hF] using D.conjugates)
  · exact exchange_coefficient_kernel_central E D hE w hw

theorem binary_kernel_annihilation_six (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (w : Group SixIndices R) (hw : pi w=1) : map φ w=1 := by
  have h₀ := exchange_coefficient_kernel_equal (D.projection 0) (D.projection 1)
    D.firstExchange rfl rfl D.firstExchange_commutes w hw
  have h₀₀ := exchange_coefficient_kernel_equal (D.doubleProjection 0 0) (D.projection 1)
    (D.secondExchange 0) rfl rfl (D.secondExchange_commutes 0) w hw
  have h₀₁ := exchange_coefficient_kernel_equal (D.doubleProjection 0 1) (D.projection 1)
    (D.secondExchange 1) rfl rfl (D.secondExchange_commutes 1) w hw
  have hsubrev : (D.doubleProjection 0 1).val*(D.doubleProjection 0 0).val=0 := by
    have hd : (D.d 1*D.d 0)*(D.s 0*D.s 0)=0 := by
      calc (D.d 1*D.d 0)*(D.s 0*D.s 0)=D.d 1*(D.d 0*D.s 0)*D.s 0 := by simp only [mul_assoc]
           _ = 0 := by rw [D.ds_same,D.d_right,D.ds_cross 1 0 (by decide)]
    change ((D.s 0*D.s 1)*(D.d 1*D.d 0))*((D.s 0*D.s 0)*(D.d 0*D.d 0))=0
    rw [mul_assoc,← mul_assoc (D.d 1*D.d 0),hd,zero_mul,mul_zero]
  have hsub := CompressedSplittings.Idempotent.steinberg_split six_three
    (D.projection 0) (D.doubleProjection 0 0) (D.doubleProjection 0 1)
    D.subsplit D.subcross hsubrev w
  rw [h₀,h₀₀,h₀₁] at hsub
  have h₁ : map (D.projection 1).coefficient w=1 :=
    mul_left_cancel (hsub.symm.trans (mul_one _).symm)
  have hsplit := CompressedSplittings.Idempotent.steinberg_split six_three
    (CompressedSplittings.full φ) (D.projection 0) (D.projection 1)
    D.split D.cross D.firstExchange.FE w
  have hfull : (CompressedSplittings.full φ).coefficient=φ := by
    ext a
    change φ a*φ 1=φ a
    rw [← map_mul,mul_one]
  rw [hfull,h₀,h₁,one_mul] at hsplit
  exact hsplit

end

variable {R S n m : Type*} [Ring R] [Ring S]

theorem binary_kernel_annihilation (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (w : Group (Fin 6) R) (hw : pi w=1) : map φ w=1 := by
  have hm : matrix w=1 := congrArg Subtype.val hw
  have hc : pi (reindex sixEquiv.symm.toEmbedding w)=1 := by
    apply Subtype.ext
    change matrix (reindex sixEquiv.symm.toEmbedding w)=1
    rw [matrix_reindex_equiv,hm,map_one]
  have h := binary_kernel_annihilation_six φ D (reindex sixEquiv.symm.toEmbedding w) hc
  have h' := congrArg (reindex (R:=R) sixEquiv.toEmbedding) h
  rw [map_reindex,reindex_equiv_symm,map_one] at h'
  exact h'

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace TorusStabilizer
open SequentialLimit SequentialAction AscendingHNN TorusAction HomStabilizer
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x)=f g • s x)
variable {J : Type*} (z : J → X) (a : U) (ha : ∀ j, a • s (z j)=z j)

lemma base_mem_iff (hs : Function.Injective s) (u : U) :
    u ∈ HNNSubgroup.base (innerTwist f a) (innerTwist_injective f hf a)
      (changedSubgroup f hf s heq z a) ↔ u ∈ stageSubgroup z := by
  change (∀ j, representation f hf s heq
    (changeStableHom f hf a (embed (innerTwist f a) (innerTwist_injective f hf a) u))
      (of s 0 (z j))=of s 0 (z j)) ↔ ∀ j, u • z j=z j
  simp only [changeStableHom_embed,representation_embed,basePerm_of,Function.iterate_zero,id_eq]
  exact forall_congr' (fun _ => (of_injective s hs 0).eq_iff)

include ha in

def torusEquiv :
    Torus (HNNSubgroup.baseMap (innerTwist f a) (innerTwist_injective f hf a)
      (changedSubgroup f hf s heq z a) (changed_stable_mem f hf s heq z a ha))
      (HNNSubgroup.baseMap_injective (innerTwist f a) (innerTwist_injective f hf a)
        (changedSubgroup f hf s heq z a) (changed_stable_mem f hf s heq z a ha)) ≃*
    limitSubgroup f hf s heq z :=
  (HNNSubgroup.equiv (innerTwist f a) (innerTwist_injective f hf a)
      (changedSubgroup f hf s heq z a) (changed_stable_mem f hf s heq z a ha)).trans
    (preimageEquiv (changeStableEquiv f hf a) (limitSubgroup f hf s heq z))

end TorusStabilizer

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HomStabilizer
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace SimpleFInftyOvergroups

structure SplittingTorusModel (G : Type) [Group G] where
  U : Type
  P : Type
  [groupU : Group U]
  [groupP : Group P]
  [finitePresentation : Group.IsFinitelyPresented P]
  f : U →* U
  injective : Function.Injective f
  α : U →* P
  b : P →* U
  factorization : f = b.comp α
  splitting₂ : ListChains.IdempotentSplittings U (ZMod 2) f
  splitting₃ : ListChains.IdempotentSplittings U (ZMod 3) f
  identification : AscendingHNN.Torus f injective ≃* G
attribute [instance] SplittingTorusModel.groupU SplittingTorusModel.groupP
  SplittingTorusModel.finitePresentation

namespace SplittingTorusModel
variable {G H X : Type} [Group G] [Group H]
def relabel (M : SplittingTorusModel G) (e : G ≃* H) : SplittingTorusModel H :=
  { M with identification := M.identification.trans e }

end SplittingTorusModel
end SimpleFInftyOvergroups

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace GermBrick

lemma restricts_refl (b : GermBrick ρ) : Restricts ρ b b := by
  refine ⟨representative ρ b,Prefix.empty,?_,?_⟩ <;> simp

lemma restricts_trans {a b c : GermBrick ρ} (hab : Restricts ρ a b) (hbc : Restricts ρ b c) :
    Restricts ρ a c := by
  obtain ⟨h,p,hc,rfl⟩ := hbc
  obtain ⟨k,q,hk,rfl⟩ := hab
  obtain ⟨α,hk'⟩ := (mk_eq_iff ρ _ _).mp hk.symm
  subst k
  refine ⟨h,p.append (q.permute (ρ α)),hc,?_⟩
  rw [LocalEmbedding.ofPrefix_append]
  simp only [LocalEmbedding.comp_assoc]
  rw [LocalEmbedding.global_ofPrefix]
  simp only [← LocalEmbedding.comp_assoc]
  exact mk_gauge ρ _ α

lemma region_subset_of_restricts {a b : GermBrick ρ} (hab : Restricts ρ a b) :
    region ρ a ⊆ region ρ b := by
  obtain ⟨h,p,rfl,rfl⟩ := hab
  rintro _ ⟨x,rfl⟩
  exact ⟨p.chart x,rfl⟩

end GermBrick

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace SteinChains
section
open OrderListChains
variable (V : Type*)

def Descending (s : Simplex (Face V)) : Prop := (list (Face V) s).Pairwise (fun F E => E ≤ F)

def faceCarrier (T : Finset V) : Submodule ℤ (Chain (Face V)) :=
  Finsupp.supported ℤ ℤ {s | Descending V s ∧ ∀ F ∈ vertices (Face V) s, F.val ⊆ T}

noncomputable def select : Chain (Face V) →ₗ[ℤ] Chain V := mapChain (Face V) (choose V)

end

open OrderListChains
variable (V : Type*)

namespace Complex
variable (K : Complex V)
def faceModule : Submodule ℤ (Chain (Face V)) :=
  Finsupp.supported ℤ ℤ {s | Descending V s ∧ ∀ F ∈ vertices (Face V) s, F.val ∈ K.faces}

end Complex

end SteinChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace GermBrick

lemma eq_of_restricts_of_region_eq {a b : GermBrick ρ} (hab : Restricts ρ a b)
    (he : region ρ a = region ρ b) : a = b := by
  obtain ⟨h,p,rfl,rfl⟩ := hab
  have hp : p.brick = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : h x ∈ region ρ (mk ρ h) := ⟨x,rfl⟩
    rw [← he] at hx
    obtain ⟨y,hy⟩ := hx
    refine ⟨y,?_⟩
    exact h.toEmbedding.injective hy
  rw [Prefix.eq_empty_of_brick_univ hp,LocalEmbedding.ofPrefix_empty,LocalEmbedding.comp_identity]

end GermBrick
namespace Basis

lemma refines_ancestor_unique {B C : Basis ρ} {c : C} {b b' : B}
    (hb : GermBrick.Restricts ρ c.1 b.1) (hb' : GermBrick.Restricts ρ c.1 b'.1) : b = b' := by
  obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ c.1
  exact eq_of_common_point ρ B (GermBrick.region_subset_of_restricts ρ hb hx)
    (GermBrick.region_subset_of_restricts ρ hb' hx)

end Basis

end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasis
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def twistPiecesToVertex (B : Basis ρ) : (B → A) →* vertexStabilizer ρ B :=
  (twistPiecesHom ρ B).codRestrict _ (fun a => rigid_le_vertexStabilizer ρ B
    (twistPiecesHom_mem_rigidStabilizer ρ B a))

noncomputable def twistPiecesToKernel (B : Basis ρ) : (B → A) →* (vertexPermutationHom ρ B).ker :=
  (twistPiecesToVertex ρ B).codRestrict _ (fun a => (mem_vertexPermutationHom_ker ρ B _).mpr
    (twistPiecesHom_mem_rigidStabilizer ρ B a))

noncomputable def vertexKernelEquiv (hρ : Function.Injective ρ) (B : Basis ρ) :
    (B → A) ≃* (vertexPermutationHom ρ B).ker :=
  MulEquiv.ofBijective (twistPiecesToKernel ρ B) ⟨fun _ _ he =>
    twistPiecesHom_injective ρ hρ B (congrArg (fun x => x.val.val) he), by
      intro g
      have hg := (mem_vertexPermutationHom_ker ρ B g.val).mp g.property
      obtain ⟨a,ha⟩ := exists_twistPiecesHom_of_mem ρ hg
      exact ⟨a,Subtype.ext (Subtype.ext ha)⟩⟩

instance vertexPermutationHom_ker_finiteIndex (B : Basis ρ) :
    (vertexPermutationHom ρ B).ker.FiniteIndex := by
  classical
  exact Subgroup.finiteIndex_ker _

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisTranslateEquiv
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

lemma glueTwo_comp (s : S) (h : Bool → LocalEmbedding ρ)
    (hd : Disjoint (Set.range (h false)) (Set.range (h true))) (b : Bool) :
    comp ρ (glueTwo ρ s h hd) (ofPrefix ρ (Prefix.cut s b)) = h b := by
  apply LocalEmbedding.ext
  exact glueTwo_chart ρ s h hd b

end LocalEmbedding
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma regions_disjoint (C : Basis ρ) {a b : C} (hab : a ≠ b) :
    Disjoint (GermBrick.region ρ a.val) (GermBrick.region ρ b.val) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hab ((C.partition x).unique hx hy)

namespace Merge
variable {ρ} {C : Basis ρ}

noncomputable def ofPair (a b : C) (hab : a ≠ b) (s : S) : Merge ρ C := by
  let h : Bool → LocalEmbedding ρ := fun q => if q then chart ρ C b else chart ρ C a
  have hd : Disjoint (Set.range (h false)) (Set.range (h true)) := by
    dsimp [h]
    rw [chart_region,chart_region]
    exact regions_disjoint ρ C hab
  exact {
    first := a
    second := b
    distinct := hab
    coordinate := s
    joined := LocalEmbedding.glueTwo ρ s h hd
    left_eq := by rw [LocalEmbedding.glueTwo_comp]; exact chart_germ ρ C a
    right_eq := by rw [LocalEmbedding.glueTwo_comp]; exact chart_germ ρ C b }

abbrev Roots (m : Merge ρ C) := Option m.Rest

noncomputable def leafEquiv (m : Merge ρ C) : Bool ⊕ m.Rest ≃ C := by
  classical
  let f : Bool ⊕ m.Rest → C := Sum.elim (fun q => if q then m.second else m.first) Subtype.val
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        cases i <;> cases j <;> simp_all [f,m.distinct,Ne.symm m.distinct]
      | inr j =>
        cases i
        · exact False.elim (j.property.1 he.symm)
        · exact False.elim (j.property.2 he.symm)
    | inr i =>
      cases j with
      | inl j =>
        cases j
        · exact False.elim (i.property.1 he)
        · exact False.elim (i.property.2 he)
      | inr j => exact congrArg Sum.inr (Subtype.ext he)
  · intro c
    by_cases hc : c = m.first
    · exact ⟨Sum.inl false,hc.symm⟩
    by_cases hd : c = m.second
    · exact ⟨Sum.inl true,hd.symm⟩
    exact ⟨Sum.inr ⟨c,hc,hd⟩,rfl⟩

noncomputable def rootChart (m : Merge ρ C) : m.Roots → LocalEmbedding ρ
  | none => m.joined
  | some c => chart ρ C c.val

lemma rootPartition (m : Merge ρ C) :
    ∀ x : Box S, ∃! r : m.Roots, x ∈ Set.range (m.rootChart r) := by
  classical
  intro x
  obtain ⟨c,hc,hu⟩ := C.partition x
  have hnone : x ∈ Set.range (m.rootChart none) ↔ c = m.first ∨ c = m.second := by
    change x ∈ Set.range m.joined ↔ _
    rw [m.range_joined]
    constructor
    · rintro (hx | hx)
      · exact Or.inl ((hu _ hx).symm)
      · exact Or.inr ((hu _ hx).symm)
    · rintro (rfl | rfl)
      · exact Or.inl hc
      · exact Or.inr hc
  have hsome (r : m.Rest) : x ∈ Set.range (m.rootChart (some r)) ↔ r.val = c := by
    change x ∈ Set.range (chart ρ C r.val) ↔ _
    rw [chart_region]
    exact ⟨hu _,fun he => by rw [he]; exact hc⟩
  by_cases h : c = m.first ∨ c = m.second
  · refine ⟨none,hnone.mpr h,?_⟩
    intro r hr
    cases r with
    | none => rfl
    | some r =>
      have he := (hsome r).mp hr
      rcases h with h | h
      · exact False.elim (r.property.1 (he.trans h))
      · exact False.elim (r.property.2 (he.trans h))
  · have hh : c ≠ m.first ∧ c ≠ m.second := not_or.mp h
    refine ⟨some ⟨c,hh⟩,(hsome _).mpr rfl,?_⟩
    intro r hr
    cases r with
    | none => exact False.elim (h (hnone.mp hr))
    | some r => exact congrArg some (Subtype.ext ((hsome r).mp hr))

noncomputable def lower (m : Merge ρ C) : Basis ρ := by
  classical
  exact ofChartPartition ρ m.rootChart m.rootPartition

end Merge
end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinGermBrick
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def descendants (C : Basis ρ) (d : GermBrick ρ) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => GermBrick.region ρ c.val ⊆ GermBrick.region ρ d)

noncomputable def intervalCode (C D : Basis ρ) : Finset (Finset C) := by
  classical
  exact Finset.univ.image (fun d : D => descendants ρ C d.val)

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def rankModel (k : ℕ) : Basis ρ := by
  classical
  exact if h : ∃ B : Basis ρ, rank ρ B = k then Classical.choose h else trivial ρ

end TwistedBrin.Basis

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

instance pairPermutationHom_ker_finiteIndex (B C : Basis ρ) :
    (pairPermutationHom ρ B C).ker.FiniteIndex := by
  classical
  exact Subgroup.finiteIndex_ker _

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPatternFactor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Forest.leaf_restricts {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) :
    GermBrick.Restricts ρ (F.leaves i).val i.1.val :=
  ⟨chart ρ B i.1,Pattern.leafPrefix (F.pattern i.1) i.2,
    (chart_germ ρ B i.1).symm,(F.chart_eq i).symm⟩

lemma Forest.pieces_eq {B C : Basis ρ} (F K : Forest ρ B C) (b : B) :
    Pattern.pieces (F.pattern b) = Pattern.pieces (K.pattern b) := by
  classical
  have help (F K : Forest ρ B C) : Pattern.pieces (F.pattern b) ⊆ Pattern.pieces (K.pattern b) := by
    intro p hp
    obtain ⟨i,rfl⟩ := (Pattern.mem_pieces _ _).mp hp
    obtain ⟨⟨b',j⟩,hj⟩ := K.leaves.surjective (F.leaves ⟨b,i⟩)
    have hr : GermBrick.Restricts ρ (F.leaves ⟨b,i⟩).val b'.val := by
      rw [← hj]
      exact K.leaf_restricts ρ ⟨b',j⟩
    have hb : b = b' := refines_ancestor_unique ρ (F.leaf_restricts ρ ⟨b,i⟩) hr
    subst b'
    apply (Pattern.mem_pieces _ _).mpr
    refine ⟨j,?_⟩
    apply GermBrick.restriction_injective ρ (chart ρ B b)
    exact (K.chart_eq ⟨b,j⟩).trans ((congrArg Subtype.val hj).trans (F.chart_eq ⟨b,i⟩).symm)
  exact Finset.Subset.antisymm (help F K) (help K F)

lemma Forest.firstCoordinates_eq {B C : Basis ρ} (F K : Forest ρ B C) (b : B) :
    Pattern.firstCoordinates (F.pattern b) = Pattern.firstCoordinates (K.pattern b) :=
  Pattern.firstCoordinates_eq_of_pieces_eq (F.pieces_eq ρ K b)

end TwistedBrin.Basis

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Forest.firstCoordinates_mono {B C D : Basis ρ} (F : Forest ρ B C)
    (K : Forest ρ C D) (H : Forest ρ B D) (b : B) :
    Pattern.firstCoordinates (F.pattern b) ⊆ Pattern.firstCoordinates (H.pattern b) := by
  rw [H.firstCoordinates_eq ρ (F.trans K) b]
  exact Pattern.firstCoordinates_graft _ _

lemma Forest.firstCoordinates_of_grid_eq {B C : Basis ρ} (F : Forest ρ B C)
    (K : B → Finset S) (h : C = gridExpansion ρ B K) (b : B) :
    Pattern.firstCoordinates (F.pattern b) = K b := by
  classical
  subst C
  simpa only [Forest.expansion,Pattern.firstCoordinates_uniform,Finset.toList_toFinset] using
    F.firstCoordinates_eq ρ (Forest.expansion B (fun b => Pattern.uniform (K b).toList)) b

lemma gridExpansion_injective (B : Basis ρ) : Function.Injective (gridExpansion ρ B) := by
  classical
  intro K L h
  funext b
  simpa only [Forest.expansion,Pattern.firstCoordinates_uniform,Finset.toList_toFinset] using
    (Forest.expansion B (fun b => Pattern.uniform (K b).toList)).firstCoordinates_of_grid_eq ρ L h b

lemma firstCuts_mono {B C D : Basis ρ} (hBC : CutRefines ρ B C) (hCD : CutRefines ρ C D)
    (hBD : CutRefines ρ B D) (b : B) : firstCuts ρ hBC b ⊆ firstCuts ρ hBD b :=
  (Classical.choice hBC).firstCoordinates_mono ρ (Classical.choice hCD) (Classical.choice hBD) b

lemma firstCuts_grid (B : Basis ρ) (K : B → Finset S) (h : CutRefines ρ B (gridExpansion ρ B K)) :
    firstCuts ρ h = K := by
  funext b
  exact (Classical.choice h).firstCoordinates_of_grid_eq ρ K rfl b

lemma gridExpansion_refines_iff {B C : Basis ρ} (h : CutRefines ρ B C) (K : B → Finset S) :
    CutRefines ρ (gridExpansion ρ B K) C ↔ ∀ b, K b ⊆ firstCuts ρ h b := by
  constructor
  · intro hKC b
    have hh := firstCuts_mono ρ (cutRefines_gridExpansion ρ B K) hKC h b
    rwa [firstCuts_grid] at hh
  · intro hh
    exact (Classical.choice h).gridExpansion_refines ρ K hh

lemma firstCore_upper {B C : Basis ρ} (h : CutRefines ρ B C) : CutRefines ρ (firstCore ρ h) C :=
  (gridExpansion_refines_iff ρ h _).mpr (fun _ _ h => h)

lemma firstCore_mono {B C D : Basis ρ} (hBC : CutRefines ρ B C) (hCD : CutRefines ρ C D)
    (hBD : CutRefines ρ B D) : CutRefines ρ (firstCore ρ hBC) (firstCore ρ hBD) :=
  gridExpansion_mono ρ B _ _ (firstCuts_mono ρ hBC hCD hBD)

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace CutInterval
variable {ρ} {B C : Basis ρ}

noncomputable def core (D : CutInterval ρ B C) : CutInterval ρ B C :=
  ⟨firstCore ρ D.lower, firstCore_lower ρ D.lower,
    cutRefines_trans ρ (firstCore_upper ρ D.lower) D.upper⟩
end CutInterval

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)

noncomputable def toInterval (K : CutSelections ρ h) : CutInterval ρ B C :=
  ⟨gridExpansion ρ B K.val,cutRefines_gridExpansion ρ B _,
    (gridExpansion_refines_iff ρ h K.val).mpr K.property⟩
noncomputable def ofInterval (D : CutInterval ρ B C) : CutSelections ρ h :=
  ⟨firstCuts ρ D.lower, firstCuts_mono ρ D.lower D.upper h⟩

lemma to_of (D : CutInterval ρ B C) : toInterval h (ofInterval h D) = D.core := by
  apply CutInterval.ext
  rfl
end CutSelections
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisFirstCut
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)

lemma grid_eq_bottom_iff (K : CutSelections ρ h) :
    (toInterval h K).val = B ↔ selected h K = ∅ := by
  constructor
  · intro hk
    have he : K = empty h := Subtype.ext (gridExpansion_injective ρ B
      (hk.trans (gridExpansion_empty ρ B).symm))
    rw [he,selected_empty]
  · intro hk
    have he : K = empty h := (booleanEquiv h).injective (hk.trans (selected_empty h).symm)
    rw [he]
    exact gridExpansion_empty ρ B

lemma grid_eq_top_iff (htop : firstCore ρ h = C) (K : CutSelections ρ h) :
    (toInterval h K).val = C ↔ selected h K = Finset.univ := by
  constructor
  · intro hk
    have he : K = full h := Subtype.ext (gridExpansion_injective ρ B (hk.trans htop.symm))
    rw [he,selected_full]
  · intro hk
    have he : K = full h := (booleanEquiv h).injective (hk.trans (selected_full h).symm)
    rw [he]
    exact htop

def Proper := {K : CutSelections ρ h // (toInterval h K).val ≠ B ∧ (toInterval h K).val ≠ C}
instance instPartialOrderProper : PartialOrder (Proper h) := inferInstanceAs
  (PartialOrder {K : CutSelections ρ h // (toInterval h K).val ≠ B ∧ (toInterval h K).val ≠ C})

noncomputable def properBooleanBoundary (htop : firstCore ρ h = C) :
    Proper h ≃o {T : Finset (FirstCut ρ h) // T ≠ ∅ ∧ T ≠ Finset.univ} where
  toFun K := ⟨selected h K.val,by
    exact ⟨fun he => K.property.1 ((grid_eq_bottom_iff h K.val).mpr he),
      fun he => K.property.2 ((grid_eq_top_iff h htop K.val).mpr he)⟩⟩
  invFun T := ⟨fromSelected h T.val,by
    exact ⟨fun he => T.property.1 ((selected_fromSelected h T.val).symm.trans
      ((grid_eq_bottom_iff h _).mp he)),
      fun he => T.property.2 ((selected_fromSelected h T.val).symm.trans
        ((grid_eq_top_iff h htop _).mp he))⟩⟩
  left_inv K := Subtype.ext (fromSelected_selected h K.val)
  right_inv T := Subtype.ext (selected_fromSelected h T.val)
  map_rel_iff' := (booleanEquiv h).map_rel_iff'

end CutSelections
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisGroundMatching
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis
section
universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

noncomputable def groundMatching (C : Basis ρ) (s : S) (k : ℕ) (hk : 2*k ≤ rank ρ C) :
    Matching C (Fin k) := by
  classical
  have hc : Fintype.card (Fin k × Bool) ≤ Fintype.card C := by
    simpa [Fintype.card_prod,rank_eq_card,Nat.mul_comm] using hk
  let e : (Fin k × Bool) ↪ C := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  exact {
    edge := fun i => Merge.ofPair (ρ := ρ) (e (i,false)) (e (i,true))
      (fun he => Bool.false_ne_true (congrArg Prod.snd (e.injective he))) s
    endpoints_injective := by
      have h (p : Fin k × Bool) :
          (Merge.ofPair (ρ := ρ) (e (p.1,false)) (e (p.1,true))
            (fun he => Bool.false_ne_true (congrArg Prod.snd (e.injective he))) s).endpoint p.2 = e p := by
        rcases p with ⟨i,⟨⟩⟩ <;> rfl
      simpa only [h] using e.injective }

end

universe w
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactSubtypeOfExactSet
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)

def globalHom : A →* localGroup ρ where
  toFun a := ⟨twist ρ a,by
    intro x
    refine ⟨Prefix.empty,Prefix.empty,a,⟨x,rfl⟩,?_⟩
    intro y
    rfl⟩
  map_one' := by
    apply Subtype.ext
    exact Equiv.ext (twist_one ρ)
  map_mul' a b := by
    apply Subtype.ext
    exact Equiv.ext (twist_mul ρ a b)

end TwistedBrin

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinEquiv
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped commutatorElement
namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace PartitionMaps
variable {I : Type} [Fintype I]

def equiv (p : I → Prefix S) (hp : IsPartition p) : I × Box S ≃ Box S :=
  Equiv.ofBijective (fun z => (p z.1).chart z.2) (by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩ he
      have hij : i=j := (hp ((p i).chart x)).unique ⟨x,rfl⟩ ⟨y,he.symm⟩
      subst j
      exact Prod.ext rfl ((p i).chart_injective he)
    · intro x
      obtain ⟨i,⟨y,hy⟩,_⟩ := hp x
      exact ⟨(i,y),hy⟩)

omit [Fintype I] in
@[simp] lemma equiv_apply [Fintype I] (p : I → Prefix S) (hp : IsPartition p) (i : I) (x : Box S) :
    equiv p hp (i,x) = (p i).chart x := rfl

def rearrange (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q) : localGroup ρ :=
  ⟨(equiv p hp).symm.trans (equiv q hq),by
    intro x
    obtain ⟨i,hix,_⟩ := hp x
    refine ⟨p i,q i,1,hix,?_⟩
    intro y
    change equiv q hq ((equiv p hp).symm (equiv p hp (i,y))) = _
    rw [Equiv.symm_apply_apply,twist_one]
    rfl⟩

omit [Fintype I] in
@[simp] lemma rearrange_chart [Fintype I] (p q : I → Prefix S) (hp : IsPartition p) (hq : IsPartition q)
    (i : I) (x : Box S) :
    (rearrange ρ p q hp hq).val ((p i).chart x) = (q i).chart x :=
  congrArg (equiv q hq) ((equiv p hp).symm_apply_apply (i,x))

def pieces (p : I → Prefix S) (hp : IsPartition p) (g : I → localGroup ρ) : localGroup ρ :=
  ⟨(equiv p hp).symm.trans ((Equiv.prodCongrRight fun i => (g i).val).trans (equiv p hp)),by
    apply locallyStandard_of_charts ρ (fun i => LocalEmbedding.ofPrefix ρ (p i))
      (fun i => LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ (p i)) (LocalEmbedding.ofGroup ρ (g i)))
    · intro x
      obtain ⟨i,⟨y,hy⟩,_⟩ := hp x
      exact ⟨i,y,hy⟩
    · intro i y
      change equiv p hp ((Equiv.prodCongrRight fun i => (g i).val)
        ((equiv p hp).symm (equiv p hp (i,y)))) = _
      rw [Equiv.symm_apply_apply]
      rfl⟩

omit [Fintype I] in
@[simp] lemma pieces_chart [Fintype I] (p : I → Prefix S) (hp : IsPartition p)
    (g : I → localGroup ρ) (i : I) (x : Box S) :
    (pieces ρ p hp g).val ((p i).chart x) = (p i).chart ((g i).val x) := by
  change equiv p hp ((Equiv.prodCongrRight fun i => (g i).val)
    ((equiv p hp).symm (equiv p hp (i,x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

omit [Fintype I] in
lemma ext [Fintype I] (p : I → Prefix S) (hp : IsPartition p) {g h : localGroup ρ}
    (he : ∀ i x, g.val ((p i).chart x) = h.val ((p i).chart x)) : g=h := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨i,⟨y,rfl⟩,_⟩ := hp x
  exact he i y

def piecesHom (p : I → Prefix S) (hp : IsPartition p) : (I → localGroup ρ) →* localGroup ρ where
  toFun := pieces ρ p hp
  map_one' := by
    apply ext ρ p hp
    intro i x
    simp only [pieces_chart,Pi.one_apply,OneMemClass.coe_one,Equiv.Perm.one_apply]
  map_mul' g h := by
    apply ext ρ p hp
    intro i x
    simp only [pieces_chart,Pi.mul_apply,Subgroup.coe_mul,Equiv.Perm.mul_apply]

@[simp] lemma piecesHom_apply (p : I → Prefix S) (hp : IsPartition p)
    (g : I → localGroup ρ) : piecesHom ρ p hp g=pieces ρ p hp g := rfl

end PartitionMaps
namespace Localization

noncomputable def gridIndex (p : Prefix S) : Prefix.Grid p.lengths :=
  Prefix.gridPoint p.lengths (p.chart (fun _ _ => false))

def hom (p : Prefix S) : localGroup ρ →* localGroup ρ := by
  classical
  exact (PartitionMaps.piecesHom ρ (Prefix.gridPrefix p.lengths) (Prefix.grid_partition _)).comp
    (MonoidHom.mulSingle (fun _ : Prefix.Grid p.lengths => localGroup ρ) (gridIndex p))

end Localization
end TwistedBrin

namespace TwistedBrin
variable {A S : Type} [Group A] (ρ : A →* Equiv.Perm S)
namespace Prefix
lemma disjoint_of_length {p q : Prefix S} {x : Box S} (hx : x ∈ q.brick)
    (hn : x ∉ p.brick) (hl : ∀ s, (p s).length ≤ (q s).length) : Disjoint p.brick q.brick := by
  apply Set.disjoint_left.mpr
  intro y hy hyq
  exact hn (brick_subset_of_extends (extends_of_mem_of_length_le hy hyq hl) hx)
end Prefix
namespace BrickSwap
variable (p q : Prefix S) (hd : Disjoint p.brick q.brick)

def fn (x : Box S) : Box S := by
  classical
  exact if x ∈ p.brick then q.chart (p.tail x)
  else if x ∈ q.brick then p.chart (q.tail x) else x

lemma chart_left (x : Box S) : fn p q (p.chart x) = q.chart x := by
  simp only [fn,Prefix.chart_mem_brick,ite_true,Prefix.tail_chart]

include hd in
lemma chart_right (x : Box S) : fn p q (q.chart x) = p.chart x := by
  have hn : q.chart x ∉ p.brick := fun hp => (Set.disjoint_left.mp hd) hp (Prefix.chart_mem_brick _ _)
  simp only [fn,hn,ite_false,Prefix.chart_mem_brick,ite_true,Prefix.tail_chart]

lemma outside (x : Box S) (hp : x ∉ p.brick) (hq : x ∉ q.brick) : fn p q x=x := by
  simp [fn,hp,hq]

include hd in
lemma involutive : Function.Involutive (fn p q) := by
  intro x
  by_cases hp : x ∈ p.brick
  · obtain ⟨y,rfl⟩ := hp
    rw [chart_left,chart_right p q hd]
  · by_cases hq : x ∈ q.brick
    · obtain ⟨y,rfl⟩ := hq
      rw [chart_right p q hd,chart_left]
    · rw [outside p q x hp hq,outside p q x hp hq]

end BrickSwap
end TwistedBrin

end
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticProduct
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.SemanticEncoding
noncomputable section
open scoped Classical
open FiniteAlgebraicEnvelopes Bootstrap
open ContextualEncoding
namespace SemanticProduct
variable {A K : Type*} [DecidableEq A] [MonoidWithZero K]
  (P : NormalPresentation (FreeMonoid A) K)

def pairEval : FreeMonoid (ProductFamily.Letter A) →* K × PartialAffine.monoid where
  toFun w := (P.q (FreeMonoid.ofList (Projection.left w.toList)),PartialAffine.wordValue (Projection.right w.toList))
  map_one' := by simp only [FreeMonoid.toList_one, Projection.left, List.filterMap_nil,
    FreeMonoid.ofList_nil, map_one]; rfl
  map_mul' u v := by
    apply Prod.ext
    · simp only [FreeMonoid.toList_mul,Projection.left_append,FreeMonoid.ofList_append,map_mul]
      rfl
    · apply Subtype.ext
      simp [PartialAffine.wordValue,PartialAffine.value]

def evaluation : FreeMonoid (ProductFamily.Letter A) →* Mon (K:=K) :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair K PartialAffine.monoid).comp (pairEval P)

omit [DecidableEq A] in
 theorem pairEval_surjective : Function.Surjective (pairEval P) := by
  rintro ⟨x,y⟩
  obtain ⟨u,rfl⟩ := P.surjective x
  obtain ⟨v,rfl⟩ := PartialAffine.wordValue_surjective y
  refine ⟨FreeMonoid.ofList (u.toList.map Sum.inl++v.map Sum.inr),?_⟩
  simp [pairEval,Projection.left,Projection.right,List.filterMap_map]

omit [DecidableEq A] in
 theorem evaluation_surjective : Function.Surjective (evaluation P) :=
  (FiniteAlgebraicEnvelopes.ZeroProduct.pair_surjective _ _).comp (pairEval_surjective P)

def normal (w : List (ProductFamily.Letter A)) : List A :=
  (P.normal (FreeMonoid.ofList (Projection.left w))).toList

def value (w : List (ProductFamily.Letter A)) : Option (ProductFamily.Key A) :=
  ProductFamily.combine P.omega.toList (normal P w,PartialAffine.testedClass (Projection.right w))

omit [DecidableEq A] in
 theorem normal_eq_iff (u v : List (ProductFamily.Letter A)) : normal P u = normal P v ↔
    P.q (FreeMonoid.ofList (Projection.left u)) = P.q (FreeMonoid.ofList (Projection.left v)) := by
  rw [P.complete]
  exact FreeMonoid.toList.injective.eq_iff

omit [DecidableEq A] in
 theorem normal_eq_zero (w : List (ProductFamily.Letter A)) : normal P w = P.omega.toList ↔
    P.q (FreeMonoid.ofList (Projection.left w)) = 0 := by
  change (P.normal (FreeMonoid.ofList (Projection.left w))).toList = P.omega.toList ↔ _
  rw [FreeMonoid.toList.injective.eq_iff,P.normal_eq_zero_iff]

 theorem value_eq_iff (u v : List (ProductFamily.Letter A)) :
    value P u = value P v ↔ evaluation P (FreeMonoid.ofList u) = evaluation P (FreeMonoid.ofList v) := by
  change value P u = value P v ↔
    FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _ = FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_iff]
  change value P u = value P v ↔
    (P.q (FreeMonoid.ofList (Projection.left u)),PartialAffine.wordValue (Projection.right u)) =
      (P.q (FreeMonoid.ofList (Projection.left v)),PartialAffine.wordValue (Projection.right v)) ∨
    P.q (FreeMonoid.ofList (Projection.left u)) = 0 ∧ P.q (FreeMonoid.ofList (Projection.left v)) = 0
  rw [Prod.ext_iff,←normal_eq_iff P,←normal_eq_zero P,←normal_eq_zero P]
  have hp : PartialAffine.wordValue (Projection.right u) = PartialAffine.wordValue (Projection.right v) ↔
      PartialAffine.testedClass (Projection.right u) = PartialAffine.testedClass (Projection.right v) := by
    rw [PartialAffine.testedClass_eq_iff]
    exact Subtype.ext_iff
  rw [hp]
  by_cases hu : normal P u = P.omega.toList <;>
    by_cases hv : normal P v = P.omega.toList <;>
    simp [value,ProductFamily.combine,hu,hv]
  aesop

 theorem value_eq_none (w : List (ProductFamily.Letter A)) :
    value P w = none ↔ evaluation P (FreeMonoid.ofList w) = 0 := by
  change value P w = none ↔ FiniteAlgebraicEnvelopes.ZeroProduct.pair _ _ _ = 0
  rw [FiniteAlgebraicEnvelopes.ZeroProduct.pair_eq_zero]
  change value P w = none ↔ P.q (FreeMonoid.ofList (Projection.left w))=0
  rw [←normal_eq_zero P]
  simp [value,ProductFamily.combine]

 theorem full (f : List A → Part (List A))
    (hf : ∀ w, (P.normal (FreeMonoid.ofList w)).toList ∈ f w)
    (w : List (ProductFamily.Letter A)) : value P w ∈ ProductFamily.test P.omega.toList f w :=
  (Part.mem_map_iff _).mpr ⟨_,hf _,rfl⟩

end SemanticProduct
end
end SimpleFInftyOvergroups.SemanticEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TwoEnlargements
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

section OneLayer
variable (K : Type) [CommRing K]
variable (V Z : Type) [Group V] [MulAction V Z]

variable {V Z}

def pairDiagrams : StageGeometry.PairDiagrams K
    (groupEmbedding (V := V) K) (pointEmbedding (Z := Z) K) where
  map := j K
  identity := rfl
  commute E P _hSum hEP hPE g h :=
    map_commute _ _ E P hEP hPE g h
  addition E P hSum hEP _hPE g := map_add _ _ E P hSum hEP g
  fixed E g z hz := map_fixes _ _ E g z hz

end OneLayer

namespace Double
variable (Q X : Type) [Group Q] [MulAction Q X]

variable {Q X}

def iota : Q →* W Q :=
  (groupEmbedding (ZMod 3)).comp (groupEmbedding (ZMod 2))

def ambientDiagrams₂ : StageGeometry.PairDiagrams (ZMod 2)
    (iota (Q := Q)) (ambientPoint (X := X)) :=
  diagramsForward (pairDiagrams (V := Q) (Z := X) (ZMod 2))
    (groupEmbedding (ZMod 3)) (pointEmbedding (ZMod 3))
    (groupEmbedding_pointEmbedding (ZMod 3))

def ambientDiagrams₃ : StageGeometry.PairDiagrams (ZMod 3)
    (iota (Q := Q)) (ambientPoint (X := X)) :=
  diagramsBackward (pairDiagrams (V := W₁ Q) (Z := Y₁ X) (ZMod 3))
    (groupEmbedding (ZMod 2)) (pointEmbedding (ZMod 2))
    (groupEmbedding_pointEmbedding (ZMod 2))

instance orbitSMul : SMul (W Q) (Y (Q := Q) (X := X)) :=
  (orbitAction (Q := Q) (X := X)).toSMul

def point (x : X) : Y (Q := Q) (X := X) :=
  Saturation.point (W := W Q) (ambientPoint (X := X)) x

def diagrams₂ : StageGeometry.PairDiagrams (ZMod 2)
    (iota (Q := Q)) (point (Q := Q) (X := X)) :=
  Saturation.diagrams _ ambientDiagrams₂

def diagrams₃ : StageGeometry.PairDiagrams (ZMod 3)
    (iota (Q := Q)) (point (Q := Q) (X := X)) :=
  Saturation.diagrams _ ambientDiagrams₃

end Double
end SourceEnlargement
end

end OAI
end


