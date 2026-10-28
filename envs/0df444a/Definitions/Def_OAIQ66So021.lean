-- Prove2me | Definitions.Def_OAIQ66So021
-- name    : OAIQ66So021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:27:40.133538+00:00
-- url     : https://prove2.me/theorems/0de22977-c890-4679-9d6b-b6e6c58a2812
-- title:
--   Definitions bundle OAIQ66So021 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 186 declarations of OpenAI's Lean: 64 definitions, 10 inductive types or structures, 7 instances and 105 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticProduct.Mon`, `OAI.SourceEnlargement.Saturation.diagrams`, `OAI.SourceEnlargement.diagramsBackward`, `OAI.SourceEnlargement.diagramsForward`, `OAI.StageGeometry.PairDiagrams`, `OAI.Steinberg.blockBalanced`, `OAI.Steinberg.blockLower`, `OAI.Steinberg.blockUpper`, `OAI.Steinberg.supported`, `OAI.TorusStabilizer.changedSubgroup`, `OAI.TorusStabilizer.limitSubgroup`, `OAI.TwistedBrin.Basis.CutBasis`, `OAI.TwistedBrin.Basis.CutBasis.Sublevel`, `OAI.TwistedBrin.Basis.CutDown`, `OAI.TwistedBrin.Basis.CutDown.Near`, `OAI.TwistedBrin.Basis.CutInterval`, `OAI.TwistedBrin.Basis.CutSelections`, `OAI.TwistedBrin.Basis.CutSelections.booleanEquiv`, `OAI.TwistedBrin.Basis.CutSelections.empty`, `OAI.TwistedBrin.Basis.CutSelections.fromSelected`, `OAI.TwistedBrin.Basis.CutSelections.full`, `OAI.TwistedBrin.Basis.CutSelections.selected`, `OAI.TwistedBrin.Basis.FirstCut`, `OAI.TwistedBrin.Basis.Forest.Index`, `OAI.TwistedBrin.Basis.Forest.compositeIndex`, `OAI.TwistedBrin.Basis.Forest.compositePattern`, `OAI.TwistedBrin.Basis.Forest.expansion`, `OAI.TwistedBrin.Basis.Forest.firstGrid`, `OAI.TwistedBrin.Basis.Forest.gauge`, `OAI.TwistedBrin.Basis.Forest.of_mem`, `OAI.TwistedBrin.Basis.Forest.pairKernelEquiv`, `OAI.TwistedBrin.Basis.Forest.prunedMerge`, `OAI.TwistedBrin.Basis.Forest.refl`, `OAI.TwistedBrin.Basis.Forest.rigidPairEquiv`, `OAI.TwistedBrin.Basis.Forest.rigidPairHom`, `OAI.TwistedBrin.Basis.Forest.trans`, `OAI.TwistedBrin.Basis.Matching`, `OAI.TwistedBrin.Basis.Matching.AvailableFaces`, `OAI.TwistedBrin.Basis.Matching.Pair`, `OAI.TwistedBrin.Basis.Matching.Present` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_AscendingHNNInnerTwist`, `FiniteType_NonunitalCompression`, `FiniteType_OrderChainsExactInOfDirected`, `FiniteType_RingExchange`, `FiniteType_Steinberg`, `FiniteType_SteinbergSixThree`, `FiniteType_TorusAction`, `FiniteType_TwistedBrin`, `FiniteType_TwistedBrinBasis`, `FiniteType_TwistedBrinBasisCutBasis`, `FiniteType_TwistedBrinBasisFirstCut`, `FiniteType_TwistedBrinBasisGroundMatching`, `FiniteType_TwistedBrinBasisTranslateEquiv`, `FiniteType_TwistedBrinGermBrick`, `FiniteType_TwistedBrinPattern`, `FiniteType_TwistedBrinPatternFactor`, `FiniteType_TwistedBrinPrefix`, `FiniteType_TwistedBrinRangeChartRestricts`, `SimpleOvergroups_SemanticProduct`, `SimpleOvergroups_TwoEnlargements`.
--
--   **Imports.** It imports the bundles `OAIQ66So010`, `OAIQ66So011`, `OAIQ66So013` and `OAIQ66So015` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ66So026`; the statement `OAI.TwistedBrin.Basis.pair_regular_products`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So010
import Definitions.Def_OAIQ66So011
import Definitions.Def_OAIQ66So013
import Definitions.Def_OAIQ66So015

section
-- module Solutions.OAIQ066_SO.FiniteType_Steinberg
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
variable (n R : Type*) [Ring R]

variable {n R}

lemma pi_surjective [Fintype n] [DecidableEq n] : Function.Surjective (pi (n:=n) (R:=R)) := by
  intro ⟨g,hg⟩
  have him : NoncommElementary.elementary (R:=R) (n:=n)≤ matrix.range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,j,h,a,rfl⟩
    exact ⟨root i j h a,matrix_root i j h a⟩
  obtain ⟨s,hs⟩ := him hg
  exact ⟨s,Subtype.ext hs⟩

end Steinberg

end

end OAI
end

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
section
variable {n R S : Type*} [Ring R] [Ring S] [Fintype n] [DecidableEq n]

lemma matrix_map (φ : R →ₙ+* S) (z : Group n R) :
    matrix (map φ z) = NonunitalCompression.units (matrixCoefficient φ) (matrix z) := by
  have he : (matrix (n:=n) (R:=S)).comp (map φ) =
      (NonunitalCompression.units (matrixCoefficient φ)).comp matrix := by
    apply hom_ext
    intro i j hij a
    simp only [MonoidHom.comp_apply, map_root, matrix_root]
    apply Units.ext
    simp only [NoncommElementary.root_val, NonunitalCompression.units_val,
      add_sub_cancel_left]
    change 1 + Matrix.single i j (φ a) = 1 + (Matrix.single i j a).map φ
    rw [Matrix.map_single _ _ _ φ]
  exact DFunLike.congr_fun he z

lemma map_preserves_kernel (φ : R →ₙ+* S) (z : Group n R) (hz : pi z = 1) :
    pi (map φ z) = 1 := by
  apply Subtype.ext
  change matrix (map φ z) = 1
  rw [matrix_map]
  have hm : matrix z = 1 := congrArg Subtype.val hz
  rw [hm, map_one]

end

variable {n m R : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma matrixBlock_root {p : Type*} [Fintype p] [DecidableEq p]
    (i j : n) (hij : i ≠ j) (a : R) :
    matrixBlock (p:=p) (NoncommElementary.root i j hij a) =
      NoncommElementary.root (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [matrixBlock, NoncommElementary.root_val, Matrix.single, Matrix.fromBlocks, Matrix.one_apply]

lemma matrix_reindex_inl {p : Type*} [Fintype p] [DecidableEq p] (z : Group n R) :
    matrix (reindex (Function.Embedding.inl : n ↪ n ⊕ p) z) = matrixBlock (matrix z) := by
  have he : (matrix (n:=n⊕p) (R:=R)).comp (reindex Function.Embedding.inl) =
      (matrixBlock (p:=p)).comp matrix := by
    apply hom_ext
    intro i j hij a
    simp only [MonoidHom.comp_apply, reindex_root, matrix_root, matrixBlock_root]
    rfl
  exact DFunLike.congr_fun he z

omit [Fintype n] [DecidableEq n] in
lemma reindex_trans {p : Type*} (f : n ↪ m) (g : m ↪ p) (z : Group n R) :
    reindex (f.trans g) z = reindex g (reindex f z) := by
  have h : reindex (R:=R) (f.trans g) = (reindex g).comp (reindex f) := by
    apply hom_ext
    intros
    simp only [MonoidHom.comp_apply, reindex_root]
    rfl
  exact DFunLike.congr_fun h z

variable [Fintype m] [DecidableEq m]

lemma matrixRelabel_root (e : n ≃ m) (i j : n) (hij : i ≠ j) (a : R) :
    matrixRelabel e (NoncommElementary.root i j hij a) =
      NoncommElementary.root (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  ext x y
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  simp [matrixRelabel_apply, NoncommElementary.root_val, Matrix.single, Matrix.one_apply]

lemma matrix_reindex_equiv (e : n ≃ m) (z : Group n R) :
    matrix (reindex e.toEmbedding z) = matrixRelabel e (matrix z) := by
  have h : (matrix (n:=m) (R:=R)).comp (reindex e.toEmbedding) =
      (matrixRelabel e).comp matrix := by
    apply hom_ext
    intro i j hij a
    simp only [MonoidHom.comp_apply, reindex_root, matrix_root, matrixRelabel_root]
    rfl
  exact DFunLike.congr_fun h z

lemma matrix_reindex_entry (f : n ↪ m) (z : Group n R) (i j : n) :
    (matrix (reindex f z)).val (f i) (f j) = (matrix z).val i j := by
  classical
  let e := embeddingCompletion f
  have hf : f = (Function.Embedding.inl : n ↪ n ⊕ ((Set.range f)ᶜ : Set m)).trans e.toEmbedding := by
    ext x
    rfl
  rw [hf, reindex_trans, matrix_reindex_equiv, matrixRelabel_apply]
  change (matrix (reindex Function.Embedding.inl z)).val (e.symm (e (Sum.inl i)))
    (e.symm (e (Sum.inl j))) = _
  rw [e.symm_apply_apply, e.symm_apply_apply, matrix_reindex_inl]
  rfl

lemma kernel_of_reindex (f : n ↪ m) (z : Group n R) (hz : pi (reindex f z) = 1) :
    pi z = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrArg (fun g : NoncommElementary.elementary (R:=R) (n:=m) =>
    g.val.val (f i) (f j)) hz
  change (matrix (reindex f z)).val (f i) (f j) = _ at h
  rw [matrix_reindex_entry] at h
  simpa [Matrix.one_apply, f.injective.eq_iff] using h

def supported (A : Set m) : Subgroup (Group m R) :=
  (reindex (R:=R) (Function.Embedding.subtype (fun x => x ∈ A))).range

omit [Fintype m] [DecidableEq m] in
lemma root_mem_supported (A : Set m) (i j : m) (hij : i ≠ j) (a : R)
    (hi : i ∈ A) (hj : j ∈ A) : root i j hij a ∈ supported A := by
  refine ⟨root (⟨i,hi⟩ : A) ⟨j,hj⟩ (by intro h; exact hij (congrArg Subtype.val h)) a, ?_⟩
  simp only [reindex_root]
  rfl

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
variable {R : Type*} [Ring R]

def blockUpper (A : Matrix (Fin 2) (Fin 2) R) : Group (Fin 2 ⊕ Fin 2) R :=
  root (Sum.inl 0) (Sum.inr 0) (by simp) (A 0 0) *
  root (Sum.inl 0) (Sum.inr 1) (by simp) (A 0 1) *
  root (Sum.inl 1) (Sum.inr 0) (by simp) (A 1 0) *
  root (Sum.inl 1) (Sum.inr 1) (by simp) (A 1 1)

def blockLower (A : Matrix (Fin 2) (Fin 2) R) : Group (Fin 2 ⊕ Fin 2) R :=
  root (Sum.inr 0) (Sum.inl 0) (by simp) (A 0 0) *
  root (Sum.inr 0) (Sum.inl 1) (by simp) (A 0 1) *
  root (Sum.inr 1) (Sum.inl 0) (by simp) (A 1 0) *
  root (Sum.inr 1) (Sum.inl 1) (by simp) (A 1 1)

lemma matrix_blockUpper (A : Matrix (Fin 2) (Fin 2) R) :
    (matrix (blockUpper A)).val = Matrix.fromBlocks 1 A 0 1 := by
  ext x y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
  | inr x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockUpper, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]

lemma matrix_blockLower (A : Matrix (Fin 2) (Fin 2) R) :
    (matrix (blockLower A)).val = Matrix.fromBlocks 1 0 A 1 := by
  ext x y
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
  | inr x =>
    cases y with
    | inl y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]
    | inr y =>
      fin_cases x <;> fin_cases y <;>
        simp [blockLower, matrix_root, Matrix.mul_apply, Fintype.sum_sum_type,
          Fin.sum_univ_two, Matrix.single, Matrix.one_apply, Matrix.fromBlocks]

def blockBalanced (U : (Matrix (Fin 2) (Fin 2) R)ˣ) : Group (Fin 2 ⊕ Fin 2) R :=
  blockUpper U.val * blockLower (-U.inv) * blockUpper U.val *
    blockUpper (-1) * blockLower 1 * blockUpper (-1)

lemma matrix_blockBalanced (U : (Matrix (Fin 2) (Fin 2) R)ˣ) :
    (matrix (blockBalanced U)).val = Matrix.fromBlocks U.val 0 0 U.inv := by
  simp only [blockBalanced, map_mul, Units.val_mul, matrix_blockUpper, matrix_blockLower]
  simp [Matrix.fromBlocks_multiply]

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

variable {R S n m : Type*} [Ring R] [Ring S]

lemma map_reindex (φ : R →ₙ+* S) (f : n ↪ m) (z : Group n R) :
    map φ (reindex f z)=reindex f (map φ z) := by
  have h : (map φ).comp (reindex f) = (reindex f).comp (map (n:=n) φ) := by
    apply hom_ext
    intro i j hij a
    simp
  exact DFunLike.congr_fun h z

lemma reindex_equiv_symm (e : n ≃ m) (z : Group m R) :
    reindex e.toEmbedding (reindex e.symm.toEmbedding z)=z := by
  rw [← reindex_trans]
  have he : e.symm.toEmbedding.trans e.toEmbedding=Function.Embedding.refl m := by
    ext i
    exact e.apply_symm_apply i
  rw [he,reindex_id]

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace TorusAction
open SequentialLimit SequentialAction AscendingHNN
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

lemma basePerm_of (g : U) (i : ℕ) (x : X) :
    basePerm f s heq g (of s i x) = of s i ((f : U → U)^[i] g • x) := by
  rw [basePerm_apply,of_advance f 0 i (Nat.zero_le i),Nat.sub_zero,act_of]

end TorusAction

end

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

def limitSubgroup : Subgroup (Torus f hf) :=
  fixedTuple (representation f hf s heq) (fun j => of s 0 (z j))

def changedSubgroup : Subgroup (Torus (innerTwist f a) (innerTwist_injective f hf a)) :=
  (limitSubgroup f hf s heq z).comap (changeStableHom f hf a)

include ha in
lemma changed_stable_mem :
    stable (innerTwist f a) (innerTwist_injective f hf a) ∈ changedSubgroup f hf s heq z a := by
  change ∀ j, representation f hf s heq
    (changeStableHom f hf a (stable (innerTwist f a) (innerTwist_injective f hf a)))
    (of s 0 (z j)) = of s 0 (z j)
  intro j
  rw [changeStableHom_stable,map_mul,map_inv,representation_stable,representation_embed]
  rw [← map_inv]
  simp only [Equiv.Perm.mul_apply,basePerm_of,Function.iterate_zero,id_eq,shift_of]
  have hz : a⁻¹ • z j = s (z j) := by
    calc a⁻¹ • z j = a⁻¹ • (a • s (z j)) := congrArg (fun x => a⁻¹ • x) (ha j).symm
         _ = s (z j) := inv_smul_smul a (s (z j))
  rw [hz,of_succ]

end TorusStabilizer

namespace StageGeometry
open StageConstruction

structure PairDiagrams {Q W X Y : Type} [Group Q] [Group W]
    [MulAction Q X] [MulAction W Y] (K : Type) [CommRing K]
    (ι : Q →* W) (point : X → Y) where
  map : BinaryPrefixOperators.idempotents K → (Q →* W)
  identity : map ⟨1,BinaryPrefixOperators.identity_mem K⟩ = ι
  commute : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ _hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 → ∀ u v, Commute (map E u) (map P v)
  addition : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 →
    ∀ u, map ⟨E.val+P.val,hSum⟩ u = map E u * map P u
  fixed : ∀ E q x, q • x = x → map E q • point x = point x

end StageGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
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
namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace LocalEmbedding
lemma comp_assoc (h k l : LocalEmbedding ρ) : comp ρ (comp ρ h k) l = comp ρ h (comp ρ k l) := rfl

end LocalEmbedding

namespace GermBrick

lemma region_nonempty (b : GermBrick ρ) : (region ρ b).Nonempty := by
  induction b using Quotient.inductionOn with | h h =>
    exact ⟨h (fun _ _ => false),⟨fun _ _ => false,rfl⟩⟩

end GermBrick
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

lemma ofPrefix_append (p q : Prefix S) :
    ofPrefix ρ (p.append q) = comp ρ (ofPrefix ρ p) (ofPrefix ρ q) := by
  apply LocalEmbedding.ext
  intro x
  exact Prefix.chart_append p q x
lemma global_ofPrefix (a : A) (p : Prefix S) :
    comp ρ (global ρ a) (ofPrefix ρ p) =
      comp ρ (ofPrefix ρ (p.permute (ρ a))) (global ρ a) := by
  apply LocalEmbedding.ext
  intro x
  exact twist_chart ρ a p x

end LocalEmbedding
namespace GermBrick

lemma mk_gauge (h : LocalEmbedding ρ) (a : A) :
    mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.global ρ a)) = mk ρ h :=
  (mk_eq_iff ρ _ _).mpr ⟨a,rfl⟩

def action : localGroup ρ →* Equiv.Perm (GermBrick ρ) where
  toFun := groupEquiv ρ
  map_one' := by apply Equiv.ext; intro b; exact map_identity ρ b
  map_mul' g h := by
    apply Equiv.ext
    intro b
    change map ρ (LocalEmbedding.ofGroup ρ (g*h)) b =
      map ρ (LocalEmbedding.ofGroup ρ g) (map ρ (LocalEmbedding.ofGroup ρ h) b)
    rw [LocalEmbedding.ofGroup_mul,map_comp]

end GermBrick

namespace Basis

noncomputable def trivial : Basis ρ := by
  classical
  exact {
    pieces := {GermBrick.mk ρ (LocalEmbedding.identity ρ)}
    partition := fun x => ⟨⟨_,Finset.mem_singleton_self _⟩,⟨x,rfl⟩,fun b _ =>
      Subtype.ext (Finset.mem_singleton.mp b.property)⟩ }

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
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

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma eq_empty_of_brick_univ {p : Prefix S} (hp : p.brick = Set.univ) : p = empty := by
  apply Prefix.ext
  intro s
  cases hs : p s with
  | nil => rfl
  | cons b l =>
    have hm : (fun (_ : S) (_ : ℕ) => !b) ∈ p.brick := hp.symm ▸ Set.mem_univ _
    have h := (mem_brick_iff_get _ _).mp hm s 0 (by simp [hs])
    cases b <;> simp [hs,Stream'.get] at h

end TwistedBrin.Prefix

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma eq_of_common_point (B : Basis ρ) {b c : B} {x : Box S}
    (hb : x ∈ GermBrick.region ρ b.1) (hc : x ∈ GermBrick.region ρ c.1) : b = c :=
  (B.partition x).unique hb hc

lemma rank_eq_card (B : Basis ρ) : rank ρ B = Fintype.card B := by
  simp only [rank,Fintype.card_coe]

lemma translate_one (B : Basis ρ) : translate ρ 1 B = B := by
  apply Basis.ext
  change B.pieces.map (GermBrick.groupEquiv ρ 1).toEmbedding = B.pieces
  have h : GermBrick.groupEquiv ρ 1 = 1 := (GermBrick.action ρ).map_one
  rw [h]
  exact Finset.map_refl

lemma translate_mul (g h : localGroup ρ) (B : Basis ρ) :
    translate ρ (g*h) B = translate ρ g (translate ρ h B) := by
  apply Basis.ext
  change B.pieces.map (GermBrick.groupEquiv ρ (g*h)).toEmbedding =
    (B.pieces.map (GermBrick.groupEquiv ρ h).toEmbedding).map (GermBrick.groupEquiv ρ g).toEmbedding
  rw [Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro b
  exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b) ((GermBrick.action ρ).map_mul g h)

noncomputable instance instMulActionSubtypePermBoxMemSubgroupLocalGroup : MulAction (localGroup ρ) (Basis ρ) where
  smul := translate ρ
  one_smul := translate_one ρ
  mul_smul := translate_mul ρ

end Basis

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma twist_injective (hρ : Function.Injective ρ) : Function.Injective (twist ρ) := by
  classical
  intro a b hab
  have he : ρ a⁻¹ = ρ b⁻¹ := by
    apply Equiv.ext
    intro s
    by_contra hn
    let x : Box S := fun t _ => decide (t = ρ a⁻¹ s)
    have hx := congrArg (fun e : Equiv.Perm (Box S) => e x s 0) hab
    change decide (ρ a⁻¹ s = ρ a⁻¹ s) = decide (ρ b⁻¹ s = ρ a⁻¹ s) at hx
    simp only [decide_true] at hx
    exact hn (of_decide_eq_true hx.symm).symm
  exact inv_injective (hρ he)

namespace Basis

noncomputable def twistPieces (B : Basis ρ) (a : B → A) : Equiv.Perm (Box S) :=
  (equivalence ρ B).symm.trans ((Equiv.prodCongrRight fun b => twist ρ (a b)).trans
    (equivalence ρ B))

lemma twistPieces_chart (B : Basis ρ) (a : B → A) (b : B) (x : Box S) :
    twistPieces ρ B a (chart ρ B b x) = chart ρ B b (twist ρ (a b) x) := by
  change equivalence ρ B ((Equiv.prodCongrRight fun b => twist ρ (a b))
    ((equivalence ρ B).symm (equivalence ρ B (b,x)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma twistPieces_isLocal (B : Basis ρ) (a : B → A) : IsLocal ρ (twistPieces ρ B a) := by
  apply locallyStandard_of_charts ρ (chart ρ B)
    (fun b => LocalEmbedding.comp ρ (chart ρ B b) (LocalEmbedding.global ρ (a b)))
  · intro x
    obtain ⟨⟨b,y⟩,hy⟩ := (equivalence ρ B).surjective x
    exact ⟨b,y,hy⟩
  · exact twistPieces_chart ρ B a

noncomputable def twistPiecesHom (B : Basis ρ) : (B → A) →* localGroup ρ where
  toFun a := ⟨twistPieces ρ B a,twistPieces_isLocal ρ B a⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨⟨b,y⟩,rfl⟩ := (equivalence ρ B).surjective x
    change twistPieces ρ B 1 (chart ρ B b y) = chart ρ B b y
    rw [twistPieces_chart]
    exact congrArg (chart ρ B b) (twist_one ρ y)
  map_mul' a c := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨⟨b,y⟩,rfl⟩ := (equivalence ρ B).surjective x
    change twistPieces ρ B (a*c) (chart ρ B b y) =
      twistPieces ρ B a (twistPieces ρ B c (chart ρ B b y))
    rw [twistPieces_chart,twistPieces_chart,twistPieces_chart]
    exact congrArg (chart ρ B b) (twist_mul ρ (a b) (c b) y)

lemma twistPiecesHom_injective (hρ : Function.Injective ρ) (B : Basis ρ) :
    Function.Injective (twistPiecesHom ρ B) := by
  intro a c he
  funext b
  apply twist_injective ρ hρ
  apply Equiv.ext
  intro x
  apply (chart ρ B b).toEmbedding.injective
  have hh := congrArg (fun g : localGroup ρ => g.val (chart ρ B b x)) he
  change twistPieces ρ B a (chart ρ B b x) = twistPieces ρ B c (chart ρ B b x) at hh
  simpa only [twistPieces_chart] using hh

def rigidStabilizer (B : Basis ρ) : Subgroup (localGroup ρ) where
  carrier := {g | ∀ b : B, GermBrick.groupEquiv ρ g b.1 = b.1}
  one_mem' := by
    intro b
    have h := (GermBrick.action ρ).map_one
    exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1) h
  mul_mem' := by
    intro g h hg hh b
    have he := congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1) ((GermBrick.action ρ).map_mul g h)
    change GermBrick.groupEquiv ρ (g*h) b.1 = GermBrick.groupEquiv ρ g (GermBrick.groupEquiv ρ h b.1) at he
    rw [he,hh b,hg b]
  inv_mem' := by
    intro g hg b
    apply (GermBrick.groupEquiv ρ g).injective
    rw [hg b]
    have h := (GermBrick.action ρ).map_inv g
    change GermBrick.groupEquiv ρ g ((GermBrick.action ρ) g⁻¹ b.1) = _
    rw [h]
    exact (GermBrick.groupEquiv ρ g).apply_symm_apply _

lemma twistPiecesHom_mem_rigidStabilizer (B : Basis ρ) (a : B → A) :
    twistPiecesHom ρ B a ∈ rigidStabilizer ρ B := by
  intro b
  rw [← GermBrick.mk_representative ρ b.1]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ _ _) = GermBrick.mk ρ _
  apply (GermBrick.mk_eq_iff ρ _ _).mpr
  refine ⟨a b,?_⟩
  apply LocalEmbedding.ext
  exact twistPieces_chart ρ B a b

lemma exists_chart_twist_of_mem_rigidStabilizer {B : Basis ρ} {g : localGroup ρ}
    (hg : g ∈ rigidStabilizer ρ B) (b : B) :
    ∃ a : A, ∀ x, g.val (chart ρ B b x) = chart ρ B b (twist ρ a x) := by
  have hh := hg b
  rw [← GermBrick.mk_representative ρ b.1] at hh
  obtain ⟨a,ha⟩ := (GermBrick.mk_eq_iff ρ _ _).mp hh
  refine ⟨a,fun x => ?_⟩
  exact congrArg (fun f : LocalEmbedding ρ => f x) ha

lemma exists_twistPiecesHom_of_mem {B : Basis ρ} {g : localGroup ρ}
    (hg : g ∈ rigidStabilizer ρ B) : ∃ a : B → A, twistPiecesHom ρ B a = g := by
  choose a ha using exists_chart_twist_of_mem_rigidStabilizer ρ hg
  refine ⟨a,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨b,y⟩,rfl⟩ := (equivalence ρ B).surjective x
  change twistPieces ρ B a (chart ρ B b y) = g.val (chart ρ B b y)
  rw [twistPieces_chart,ha b y]

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasis
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

noncomputable def vertexStabilizer (B : Basis ρ) : Subgroup (localGroup ρ) :=
  MulAction.stabilizer (localGroup ρ) B

lemma rigid_le_vertexStabilizer (B : Basis ρ) : rigidStabilizer ρ B ≤ vertexStabilizer ρ B := by
  intro g hg
  apply MulAction.mem_stabilizer_iff.mpr
  apply Basis.ext
  change B.pieces.map (GermBrick.groupEquiv ρ g).toEmbedding = B.pieces
  apply Finset.ext
  intro b
  constructor
  · intro hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_map.mp hb
    change GermBrick.groupEquiv ρ g c ∈ B.pieces
    rw [hg ⟨c,hc⟩]
    exact hc
  · intro hb
    exact Finset.mem_map.mpr ⟨b,hb,hg ⟨b,hb⟩⟩

lemma vertex_mem_iff (B : Basis ρ) (g : vertexStabilizer ρ B) (b : GermBrick ρ) :
    b ∈ B.pieces ↔ GermBrick.groupEquiv ρ g.val b ∈ B.pieces := by
  have he : B.pieces.map (GermBrick.groupEquiv ρ g.val).toEmbedding = B.pieces :=
    congrArg Basis.pieces (MulAction.mem_stabilizer_iff.mp g.property)
  constructor
  · intro hb
    rw [← he]
    exact Finset.mem_map.mpr ⟨b,hb,rfl⟩
  · intro hb
    rw [← he] at hb
    obtain ⟨c,hc,hcb⟩ := Finset.mem_map.mp hb
    have hh : c = b := (GermBrick.groupEquiv ρ g.val).injective hcb
    exact hh ▸ hc

noncomputable def vertexPermutationHom (B : Basis ρ) : vertexStabilizer ρ B →* Equiv.Perm B where
  toFun g := (GermBrick.groupEquiv ρ g.val).subtypeEquiv (vertex_mem_iff ρ B g)
  map_one' := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1) ((GermBrick.action ρ).map_one)
  map_mul' g h := by
    apply Equiv.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm (GermBrick ρ) => e b.1)
      ((GermBrick.action ρ).map_mul g.val h.val)

lemma mem_vertexPermutationHom_ker (B : Basis ρ) (g : vertexStabilizer ρ B) :
    g ∈ (vertexPermutationHom ρ B).ker ↔ g.val ∈ rigidStabilizer ρ B := by
  change vertexPermutationHom ρ B g = 1 ↔ ∀ b : B, _
  constructor
  · intro hg b
    exact congrArg (fun e : Equiv.Perm B => (e b).1) hg
  · intro hg
    apply Equiv.ext
    intro b
    exact Subtype.ext (hg b)

end TwistedBrin.Basis

namespace TwistedBrin

namespace Pattern
variable {S : Type u}

lemma split_prefix_nonempty (s : S) (P Q : Pattern S) (i : Leaves (.split s P Q)) :
    leafPrefix (.split s P Q) i s ≠ [] := by
  classical
  cases i with
  | inl i => simp [leafPrefix]
  | inr i => simp [leafPrefix]

lemma partition (P : Pattern S) : ∀ x : Box S, ∃! i : Leaves P, x ∈ (leafPrefix P i).brick := by
  induction P with
  | leaf =>
    intro x
    exact ⟨(),by simp [leafPrefix],fun i _ => by cases i; rfl⟩
  | split s P Q hP hQ =>
    intro x
    cases hx : (x s).get 0 with
    | false =>
      obtain ⟨i,hi,hu⟩ := hP ((Prefix.cut s false).tail x)
      refine ⟨Sum.inl i,?_,?_⟩
      · exact (Prefix.mem_append_iff _ _ _).mpr ⟨(Prefix.mem_cut_iff _ _ _).mpr hx,hi⟩
      · intro j hj
        cases j with
        | inl j =>
          exact congrArg Sum.inl (hu j ((Prefix.mem_append_iff _ _ _).mp hj).2)
        | inr j =>
          have hf := (Prefix.mem_cut_iff s true x).mp ((Prefix.mem_append_iff _ _ _).mp hj).1
          simp only [hx,Bool.false_eq_true] at hf
    | true =>
      obtain ⟨i,hi,hu⟩ := hQ ((Prefix.cut s true).tail x)
      refine ⟨Sum.inr i,?_,?_⟩
      · exact (Prefix.mem_append_iff _ _ _).mpr ⟨(Prefix.mem_cut_iff _ _ _).mpr hx,hi⟩
      · intro j hj
        cases j with
        | inr j =>
          exact congrArg Sum.inr (hu j ((Prefix.mem_append_iff _ _ _).mp hj).2)
        | inl j =>
          have hf := (Prefix.mem_cut_iff s false x).mp ((Prefix.mem_append_iff _ _ _).mp hj).1
          simp only [hx,Bool.true_eq_false] at hf

noncomputable def pieces (P : Pattern S) : Finset (Prefix S) := by
  classical
  exact Finset.univ.image (leafPrefix P)

lemma mem_pieces (P : Pattern S) (p : Prefix S) : p ∈ pieces P ↔ ∃ i, leafPrefix P i = p := by
  classical
  simp only [pieces,Finset.mem_image,Finset.mem_univ,true_and]

end Pattern
end TwistedBrin

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma rank_ofChartPartition {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ)
    (hp : ∀ x : Box S, ∃! i : I, x ∈ Set.range (h i)) :
    rank ρ (ofChartPartition ρ h hp) = Fintype.card I := by
  classical
  exact (Finset.card_image_of_injective _ (chartPartition_injective ρ h hp)).trans
    (Finset.card_univ)

lemma expanded_partition (B : Basis ρ) (P : B → Pattern S) :
    ∀ x : Box S, ∃! i : Σ b : B, Pattern.Leaves (P b),
      x ∈ Set.range (expandedChart ρ B P i) := by
  intro x
  obtain ⟨b,hb,hu⟩ := B.partition x
  rw [← chart_region ρ B b] at hb
  obtain ⟨y,rfl⟩ := hb
  obtain ⟨i,hi,hiu⟩ := Pattern.partition (P b) y
  refine ⟨⟨b,i⟩,?_,?_⟩
  · obtain ⟨z,rfl⟩ := hi
    exact ⟨z,rfl⟩
  · rintro ⟨c,j⟩ ⟨z,hz⟩
    have hc : (chart ρ B b) y ∈ GermBrick.region ρ c.val := by
      rw [← chart_region ρ B c]
      exact ⟨_,hz⟩
    have hb' : (chart ρ B b) y ∈ GermBrick.region ρ b.val := by
      rw [← chart_region ρ B b]
      exact ⟨y,rfl⟩
    have hcb : c = b := hu c hc
    subst c
    have hy : (Pattern.leafPrefix (P b) j).chart z = y :=
      (chart ρ B b).toEmbedding.injective hz
    have hji : j = i := hiu j ⟨z,hy⟩
    subst j
    rfl

noncomputable def expand (B : Basis ρ) (P : B → Pattern S) : Basis ρ :=
  ofChartPartition ρ (expandedChart ρ B P) (expanded_partition ρ B P)

lemma expand_leaf (B : Basis ρ) : expand ρ B (fun _ => .leaf) = B := by
  apply Basis.ext
  classical
  ext b
  change (b ∈ Finset.univ.image _) ↔ b ∈ B.pieces
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨c,i⟩,rfl⟩
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B c)
      (LocalEmbedding.ofPrefix ρ Prefix.empty)) ∈ B.pieces
    simp [chart]
  · intro hb
    refine ⟨⟨⟨b,hb⟩,PUnit.unit⟩,?_⟩
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B ⟨b,hb⟩)
      (LocalEmbedding.ofPrefix ρ Prefix.empty)) = b
    simp [chart]

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPrefix
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

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma relabel_prefix (σ : Equiv.Perm S) (P : Pattern S) (i : Leaves P) :
    leafPrefix (relabel σ P) (relabelLeaves σ P i) = (leafPrefix P i).permute σ := by
  induction P with
  | leaf => simp [relabel,relabelLeaves,leafPrefix]
  | split s P Q ihP ihQ =>
    cases i with
    | inl i =>
      change (Prefix.cut (σ s) false).append _ =
        ((Prefix.cut s false).append (leafPrefix P i)).permute σ
      rw [Prefix.permute_append,Prefix.permute_cut,ihP]
    | inr i =>
      change (Prefix.cut (σ s) true).append _ =
        ((Prefix.cut s true).append (leafPrefix Q i)).permute σ
      rw [Prefix.permute_append,Prefix.permute_cut,ihQ]

lemma graft_prefix (P : Pattern S) (Q : Leaves P → Pattern S)
    (i : Leaves P) (j : Leaves (Q i)) :
    leafPrefix (graft P Q) (graftLeaves P Q ⟨i,j⟩) =
      (leafPrefix P i).append (leafPrefix (Q i) j) := by
  induction P with
  | leaf => cases i; exact (Prefix.empty_append _).symm
  | split s P R ihP ihR =>
    cases i with
    | inl i =>
      change (Prefix.cut s false).append _ =
        ((Prefix.cut s false).append _).append _
      rw [ihP,Prefix.append_assoc]
    | inr i =>
      change (Prefix.cut s true).append _ =
        ((Prefix.cut s true).append _).append _
      rw [ihR,Prefix.append_assoc]
end TwistedBrin.Pattern

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

namespace Forest
variable {ρ}

abbrev Index {B C : Basis ρ} (F : Forest ρ B C) := Σ b : B, Pattern.Leaves (F.pattern b)

noncomputable def refl (B : Basis ρ) : Forest ρ B B where
  pattern := fun _ => .leaf
  leaves := {
    toFun := Sigma.fst
    invFun := fun b => ⟨b,()⟩
    left_inv := by rintro ⟨b,⟨⟩⟩; rfl
    right_inv := fun _ => rfl }
  chart_eq := by
    rintro ⟨b,i⟩
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
      (LocalEmbedding.ofPrefix ρ Prefix.empty)) = b.val
    simp [chart]

noncomputable def expansion (B : Basis ρ) (P : B → Pattern S) : Forest ρ B (expand ρ B P) := by
  classical
  let f : (Σ b : B, Pattern.Leaves (P b)) → expand ρ B P :=
    fun i => ⟨GermBrick.mk ρ (expandedChart ρ B P i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      exact chartPartition_injective ρ _ (expanded_partition ρ B P) (congrArg Subtype.val he)
    · intro c
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp c.property
      exact ⟨i,Subtype.ext hi⟩
  exact ⟨P,Equiv.ofBijective f hf,fun _ => rfl⟩

lemma exists_gauge {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) :
    ∃ a : A, chart ρ C (F.leaves i) = LocalEmbedding.comp ρ
      (expandedChart ρ B F.pattern i) (LocalEmbedding.global ρ a) := by
  apply (GermBrick.mk_eq_iff ρ _ _).mp
  rw [show GermBrick.mk ρ (chart ρ C (F.leaves i)) = (F.leaves i).val by
    exact GermBrick.mk_representative ρ _]
  exact (F.chart_eq i).symm

noncomputable def gauge {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) : A :=
  (F.exists_gauge i).choose

lemma gauge_spec {B C : Basis ρ} (F : Forest ρ B C) (i : F.Index) :
    chart ρ C (F.leaves i) = LocalEmbedding.comp ρ
      (expandedChart ρ B F.pattern i) (LocalEmbedding.global ρ (F.gauge i)) :=
  (F.exists_gauge i).choose_spec

noncomputable def compositePattern {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D)
    (b : B) : Pattern S :=
  Pattern.graft (F.pattern b) (fun i =>
    Pattern.relabel (ρ (F.gauge ⟨b,i⟩)) (K.pattern (F.leaves ⟨b,i⟩)))

noncomputable def compositeIndex {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D) :
    (Σ i : F.Index, Pattern.Leaves (K.pattern (F.leaves i))) ≃
      (Σ b : B, Pattern.Leaves (F.compositePattern K b)) :=
  (Equiv.sigmaCongrRight (fun i => Pattern.relabelLeaves (ρ (F.gauge i))
    (K.pattern (F.leaves i)))).trans
    ((Equiv.sigmaAssoc (fun b i => Pattern.Leaves
      (Pattern.relabel (ρ (F.gauge ⟨b,i⟩)) (K.pattern (F.leaves ⟨b,i⟩))))).trans
    (Equiv.sigmaCongrRight (fun b => Pattern.graftLeaves (F.pattern b)
      (fun i => Pattern.relabel (ρ (F.gauge ⟨b,i⟩)) (K.pattern (F.leaves ⟨b,i⟩))))))

lemma composite_chart {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D)
    (i : F.Index) (j : Pattern.Leaves (K.pattern (F.leaves i))) :
    GermBrick.mk ρ (expandedChart ρ B (F.compositePattern K) (F.compositeIndex K ⟨i,j⟩)) =
      GermBrick.mk ρ (expandedChart ρ C K.pattern ⟨F.leaves i,j⟩) := by
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B i.1)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ (Pattern.graftLeaves (F.pattern i.1)
      (fun k => Pattern.relabel (ρ (F.gauge ⟨i.1,k⟩)) (K.pattern (F.leaves ⟨i.1,k⟩)))
      ⟨i.2,Pattern.relabelLeaves (ρ (F.gauge i)) (K.pattern (F.leaves i)) j⟩)))) = _
  rw [Pattern.graft_prefix,Pattern.relabel_prefix,LocalEmbedding.ofPrefix_append]
  change GermBrick.mk ρ _ = GermBrick.mk ρ
    (LocalEmbedding.comp ρ (chart ρ C (F.leaves i))
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (K.pattern (F.leaves i)) j)))
  rw [F.gauge_spec,LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix]
  simp only [← LocalEmbedding.comp_assoc]
  rw [GermBrick.mk_gauge]
  rfl

noncomputable def trans {B C D : Basis ρ} (F : Forest ρ B C) (K : Forest ρ C D) : Forest ρ B D where
  pattern := F.compositePattern K
  leaves := (F.compositeIndex K).symm.trans ((Equiv.sigmaCongrLeft F.leaves).trans K.leaves)
  chart_eq := by
    intro k
    obtain ⟨⟨i,j⟩,rfl⟩ := (F.compositeIndex K).surjective k
    rw [F.composite_chart K i j]
    change GermBrick.mk ρ (expandedChart ρ C K.pattern ⟨F.leaves i,j⟩) =
      (K.leaves (Equiv.sigmaCongrLeft F.leaves
        ((F.compositeIndex K).symm (F.compositeIndex K ⟨i,j⟩)))).val
    rw [Equiv.symm_apply_apply]
    exact K.chart_eq ⟨F.leaves i,j⟩

end Forest

lemma cutRefines_refl (B : Basis ρ) : CutRefines ρ B B := ⟨Forest.refl B⟩
lemma cutRefines_trans {B C D : Basis ρ} (hBC : CutRefines ρ B C) (hCD : CutRefines ρ C D) :
    CutRefines ρ B D := by
  obtain ⟨F⟩ := hBC
  obtain ⟨K⟩ := hCD
  exact ⟨F.trans K⟩

end Basis
end TwistedBrin

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma uniform_length [DecidableEq S] (L : List S) (i : Leaves (uniform L)) (s : S) :
    (leafPrefix (uniform L) i s).length = L.count s := by
  induction L with
  | nil => simp [uniform,leafPrefix]
  | cons t L ih =>
    cases i with
    | inl i =>
      change ((Prefix.cut t false).append (leafPrefix (uniform L) i) s).length = _
      rw [Prefix.append_apply,List.length_append,ih]
      by_cases h : t = s
      · subst t; simp [Prefix.cut_apply,Nat.add_comm]
      · simp [Prefix.cut_apply,h,Ne.symm h]
    | inr i =>
      change ((Prefix.cut t true).append (leafPrefix (uniform L) i) s).length = _
      rw [Prefix.append_apply,List.length_append,ih]
      by_cases h : t = s
      · subst t; simp [Prefix.cut_apply,Nat.add_comm]
      · simp [Prefix.cut_apply,h,Ne.symm h]

end TwistedBrin.Pattern

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis
namespace Forest

noncomputable def of_mem {B C : Basis ρ} (P : B → Pattern S)
    (hm : ∀ i, GermBrick.mk ρ (expandedChart ρ B P i) ∈ C.pieces) : Forest ρ B C := by
  classical
  let f : (Σ b : B, Pattern.Leaves (P b)) → C := fun i => ⟨_,hm i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact chartPartition_injective ρ _ (expanded_partition ρ B P) (congrArg Subtype.val hij)
    · intro c
      let x : Box S := chart ρ C c (fun _ _ => false)
      have hc : x ∈ GermBrick.region ρ c.val := by
        rw [← chart_region]
        exact ⟨_,rfl⟩
      obtain ⟨i,hi,_⟩ := expanded_partition ρ B P x
      have hfi : x ∈ GermBrick.region ρ (f i).val := hi
      exact ⟨i,(C.partition x).unique hfi hc⟩
  exact ⟨P,Equiv.ofBijective f hf,fun _ => rfl⟩

end Forest

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisTranslateEquiv
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

lemma translate_chart_gauge (g : localGroup ρ) (B : Basis ρ) (b : B) :
    ∃ a : A, chart ρ (translate ρ g B) (translateEquiv ρ g B b) =
      LocalEmbedding.comp ρ (LocalEmbedding.comp ρ (LocalEmbedding.ofGroup ρ g)
        (chart ρ B b)) (LocalEmbedding.global ρ a) := by
  apply (GermBrick.mk_eq_iff ρ _ _).mp
  change GermBrick.mk ρ (GermBrick.representative ρ _) =
    GermBrick.map ρ (LocalEmbedding.ofGroup ρ g)
      (GermBrick.mk ρ (GermBrick.representative ρ b.val))
  simp only [GermBrick.mk_representative]
  rfl

lemma translate_cutRefines (g : localGroup ρ) {B C : Basis ρ}
    (hBC : CutRefines ρ B C) : CutRefines ρ (translate ρ g B) (translate ρ g C) := by
  classical
  obtain ⟨F⟩ := hBC
  choose a ha using translate_chart_gauge ρ g B
  let e := translateEquiv ρ g B
  let P := fun c : translate ρ g B =>
    Pattern.relabel (ρ (a (e.symm c))⁻¹) (F.pattern (e.symm c))
  apply Nonempty.intro
  apply Forest.of_mem ρ P
  rintro ⟨c,j⟩
  let b := e.symm c
  have hroot : chart ρ (translate ρ g B) c =
      LocalEmbedding.comp ρ (LocalEmbedding.comp ρ (LocalEmbedding.ofGroup ρ g)
        (chart ρ B b)) (LocalEmbedding.global ρ (a b)) := by
    have hh := ha b
    change chart ρ (translate ρ g B) (e (e.symm c)) = _ at hh
    rwa [e.apply_symm_apply] at hh
  obtain ⟨k,rfl⟩ := (Pattern.relabelLeaves (ρ (a b)⁻¹) (F.pattern b)).surjective j
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ (translate ρ g B) c)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix
      (Pattern.relabel (ρ (a b)⁻¹) (F.pattern b))
        (Pattern.relabelLeaves (ρ (a b)⁻¹) (F.pattern b) k)))) ∈ _
  rw [Pattern.relabel_prefix,hroot,LocalEmbedding.comp_assoc,
    LocalEmbedding.global_ofPrefix,twist_prefix_inv,← LocalEmbedding.comp_assoc,
    GermBrick.mk_gauge,LocalEmbedding.comp_assoc]
  change GermBrick.groupEquiv ρ g
    (GermBrick.mk ρ (expandedChart ρ B F.pattern ⟨b,k⟩)) ∈ _
  rw [F.chart_eq]
  exact Finset.mem_map.mpr ⟨_,(F.leaves ⟨b,k⟩).property,rfl⟩

end TwistedBrin.Basis

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

noncomputable def glueTwo (s : S) (h : Bool → LocalEmbedding ρ)
    (hd : Disjoint (Set.range (h false)) (Set.range (h true))) : LocalEmbedding ρ := by
  let f : Bool × Box S → Box S := fun z => h z.1 z.2
  have hf : Function.Injective f := by
    rintro ⟨b,x⟩ ⟨c,y⟩ he
    cases b <;> cases c
    · congr 1
      exact (h false).toEmbedding.injective he
    · exact False.elim ((Set.disjoint_left.mp hd) ⟨x,rfl⟩ ⟨y,he.symm⟩)
    · exact False.elim ((Set.disjoint_left.mp hd) ⟨y,he.symm⟩ ⟨x,rfl⟩)
    · congr 1
      exact (h true).toEmbedding.injective he
  let g : Box S → Box S := f ∘ (Prefix.splitEquiv s).symm
  have hg (b : Bool) (x : Box S) : g ((Prefix.cut s b).chart x) = h b x := by
    change f ((Prefix.splitEquiv s).symm (Prefix.splitEquiv s (b,x))) = _
    rw [Equiv.symm_apply_apply]
  exact {
    toEmbedding := ⟨g,hf.comp (Prefix.splitEquiv s).symm.injective⟩
    locally_standard := locallyStandard_of_charts ρ
      (fun b : Bool => ofPrefix ρ (Prefix.cut s b)) h
      (fun x => by
        obtain ⟨⟨b,y⟩,hy⟩ := (Prefix.splitEquiv s).surjective x
        exact ⟨b,y,hy⟩) g hg }

@[simp] lemma glueTwo_chart (s : S) (h : Bool → LocalEmbedding ρ)
    (hd : Disjoint (Set.range (h false)) (Set.range (h true))) (b : Bool) (x : Box S) :
    glueTwo ρ s h hd ((Prefix.cut s b).chart x) = h b x := by
  change h ((Prefix.splitEquiv s).symm (Prefix.splitEquiv s (b,x))).1
    ((Prefix.splitEquiv s).symm (Prefix.splitEquiv s (b,x))).2 = _
  rw [Equiv.symm_apply_apply]

end LocalEmbedding
namespace Basis

noncomputable def chartPartitionEquiv {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ) (hp : ∀ x : Box S, ∃! i, x ∈ Set.range (h i)) :
    I ≃ ofChartPartition ρ h hp := by
  classical
  let f : I → ofChartPartition ρ h hp := fun i =>
    ⟨GermBrick.mk ρ (h i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    exact chartPartition_injective ρ h hp (congrArg Subtype.val he)
  · intro b
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp b.property
    exact ⟨i,Subtype.ext hi⟩

@[simp] lemma chartPartitionEquiv_val {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ) (hp : ∀ x : Box S, ∃! i, x ∈ Set.range (h i)) (i : I) :
    (chartPartitionEquiv ρ h hp i).val = GermBrick.mk ρ (h i) := rfl

lemma cutRefines_ofChartPartition {I : Type*} [Fintype I]
    (h : I → LocalEmbedding ρ) (hp : ∀ x : Box S, ∃! i, x ∈ Set.range (h i))
    (C : Basis ρ) (P : I → Pattern S)
    (hm : ∀ i j, GermBrick.mk ρ (LocalEmbedding.comp ρ (h i)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P i) j))) ∈ C.pieces) :
    CutRefines ρ (ofChartPartition ρ h hp) C := by
  classical
  let B := ofChartPartition ρ h hp
  let e := chartPartitionEquiv ρ h hp
  have hg (i : I) : ∃ a : A, chart ρ B (e i) =
      LocalEmbedding.comp ρ (h i) (LocalEmbedding.global ρ a) := by
    apply (GermBrick.mk_eq_iff ρ _ _).mp
    exact GermBrick.mk_representative ρ _
  choose a ha using hg
  let Q := fun b : B => Pattern.relabel (ρ (a (e.symm b))⁻¹) (P (e.symm b))
  apply Nonempty.intro
  apply Forest.of_mem ρ Q
  rintro ⟨b,j⟩
  let i := e.symm b
  have hroot : chart ρ B b = LocalEmbedding.comp ρ (h i) (LocalEmbedding.global ρ (a i)) := by
    have hh := ha i
    change chart ρ B (e (e.symm b)) = _ at hh
    rwa [e.apply_symm_apply] at hh
  obtain ⟨k,rfl⟩ := (Pattern.relabelLeaves (ρ (a i)⁻¹) (P i)).surjective j
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (Pattern.relabel (ρ (a i)⁻¹) (P i))
      (Pattern.relabelLeaves (ρ (a i)⁻¹) (P i) k)))) ∈ _
  rw [Pattern.relabel_prefix,hroot,LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,
    twist_prefix_inv,← LocalEmbedding.comp_assoc,GermBrick.mk_gauge]
  exact hm i k

end Basis
end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma chart_germ (C : Basis ρ) (c : C) : GermBrick.mk ρ (chart ρ C c) = c.val :=
  GermBrick.mk_representative ρ _

structure Merge (C : Basis ρ) where
  first : C
  second : C
  distinct : first ≠ second
  coordinate : S
  joined : LocalEmbedding ρ
  left_eq : GermBrick.mk ρ (LocalEmbedding.comp ρ joined
    (LocalEmbedding.ofPrefix ρ (Prefix.cut coordinate false))) = first.val
  right_eq : GermBrick.mk ρ (LocalEmbedding.comp ρ joined
    (LocalEmbedding.ofPrefix ρ (Prefix.cut coordinate true))) = second.val

namespace Merge
variable {ρ} {C : Basis ρ}

lemma range_joined (m : Merge ρ C) : Set.range m.joined =
    GermBrick.region ρ m.first.val ∪ GermBrick.region ρ m.second.val := by
  have h (q : Bool) : Set.range (fun x => m.joined ((Prefix.cut m.coordinate q).chart x)) =
      GermBrick.region ρ (if q then m.second.val else m.first.val) := by
    cases q
    · change GermBrick.region ρ (GermBrick.mk ρ (LocalEmbedding.comp ρ m.joined
        (LocalEmbedding.ofPrefix ρ (Prefix.cut m.coordinate false)))) = _
      simp only [m.left_eq,Bool.false_eq_true,ite_false]
    · change GermBrick.region ρ (GermBrick.mk ρ (LocalEmbedding.comp ρ m.joined
        (LocalEmbedding.ofPrefix ρ (Prefix.cut m.coordinate true)))) = _
      simp only [m.right_eq,ite_true]
  have h0 := h false
  have h1 := h true
  simp only [Bool.false_eq_true,ite_false,ite_true] at h0 h1
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨⟨q,z⟩,rfl⟩ := (Prefix.splitEquiv m.coordinate).surjective y
    have hz : m.joined ((Prefix.cut m.coordinate q).chart z) ∈
        GermBrick.region ρ (if q then m.second.val else m.first.val) := by
      rw [← h q]; exact ⟨z,rfl⟩
    cases q
    · exact Or.inl hz
    · exact Or.inr hz
  · intro hx
    rcases hx with hx | hx
    · rw [← h0] at hx
      obtain ⟨y,rfl⟩ := hx
      exact ⟨_,rfl⟩
    · rw [← h1] at hx
      obtain ⟨y,rfl⟩ := hx
      exact ⟨_,rfl⟩

abbrev Rest (m : Merge ρ C) := {c : C // c ≠ m.first ∧ c ≠ m.second}

end Merge
end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPattern
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
namespace TwistedBrin.Pattern
variable {S : Type u}

structure Pruning (P : Pattern S) where
  shorter : Pattern S
  stem : Prefix S
  coordinate : S
  first : Leaves P
  second : Leaves P
  distinct : first ≠ second
  first_prefix : leafPrefix P first = stem.append (Prefix.cut coordinate false)
  second_prefix : leafPrefix P second = stem.append (Prefix.cut coordinate true)
  remaining : ∀ i : Leaves shorter, leafPrefix shorter i = stem ∨
    ∃ j : Leaves P, leafPrefix shorter i = leafPrefix P j ∧ j ≠ first ∧ j ≠ second

end TwistedBrin.Pattern

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Basis.Forest
variable {B C : Basis ρ}

noncomputable def prunedMerge (F : Forest ρ B C) (b : B) (T : Pattern.Pruning (F.pattern b)) :
    Merge ρ C where
  first := F.leaves ⟨b,T.first⟩
  second := F.leaves ⟨b,T.second⟩
  distinct := by
    intro he
    have hh := F.leaves.injective he
    exact T.distinct (by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh)
  coordinate := T.coordinate
  joined := LocalEmbedding.comp ρ (chart ρ B b) (LocalEmbedding.ofPrefix ρ T.stem)
  left_eq := by
    rw [LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,← T.first_prefix]
    exact F.chart_eq ⟨b,T.first⟩
  right_eq := by
    rw [LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,← T.second_prefix]
    exact F.chart_eq ⟨b,T.second⟩

end Basis.Forest
end

end TwistedBrin

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma twistPieces_expanded_germ (B : Basis ρ) (P : B → Pattern S) (a : B → A)
    (i : Σ b : B, Pattern.Leaves (P b)) :
    GermBrick.groupEquiv ρ (twistPiecesHom ρ B a)
      (GermBrick.mk ρ (expandedChart ρ B P i)) =
    GermBrick.mk ρ (expandedChart ρ B (fun b => Pattern.relabel (ρ (a b)) (P b))
      ⟨i.1,Pattern.relabelLeaves (ρ (a i.1)) (P i.1) i.2⟩) := by
  apply (GermBrick.mk_eq_iff ρ _ _).mpr
  refine ⟨a i.1,?_⟩
  apply LocalEmbedding.ext
  intro x
  change twistPieces ρ B a (chart ρ B i.1 ((Pattern.leafPrefix (P i.1) i.2).chart x)) =
    chart ρ B i.1 ((Pattern.leafPrefix (Pattern.relabel (ρ (a i.1)) (P i.1))
      (Pattern.relabelLeaves (ρ (a i.1)) (P i.1) i.2)).chart (twist ρ (a i.1) x))
  rw [twistPieces_chart,Pattern.relabel_prefix,twist_chart]

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma length_le_of_brick_subset {p q : Prefix S} (h : p.brick ⊆ q.brick) (s : S) :
    (q s).length ≤ (p s).length := by
  by_contra hn
  have hn' : (p s).length < (q s).length := by omega
  let b : Bool := (q s)[(p s).length]
  have hx := (mem_brick_iff_get q (p.chart (fun _ => Stream'.const (!b)))).mp
    (h (chart_mem_brick p _)) s (p s).length hn'
  change (Stream'.appendStream' (p s) (Stream'.const (!b))).get (p s).length = b at hx
  rw [Stream'.get_append_length] at hx
  simp [Stream'.get,Stream'.const] at hx

lemma brick_injective : Function.Injective (brick : Prefix S → Set (Box S)) := by
  intro p q he
  have hl : ∀ s, (p s).length = (q s).length := fun s =>
    Nat.le_antisymm (length_le_of_brick_subset he.symm.subset s)
      (length_le_of_brick_subset he.subset s)
  let x := p.chart (fun _ _ => false)
  have hp := (mem_brick_iff p x).mp (chart_mem_brick p _)
  have hq := (mem_brick_iff q x).mp (he ▸ chart_mem_brick p _)
  apply Prefix.ext
  intro s
  exact (hp s).symm.trans ((congrArg (fun n => Stream'.take n (x s)) (hl s)).trans (hq s))

end TwistedBrin.Prefix

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinGermBrick
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

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma append_left_cancel (p : Prefix S) {q r : Prefix S} (h : p.append q = p.append r) : q = r := by
  apply Prefix.ext
  intro s
  have he := congrArg (fun t : Prefix S => t s) h
  exact List.append_cancel_left he

end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma root_fixed_of_prefixes_fixed (σ : Equiv.Perm S) (s : S) (P Q : Pattern S)
    (h : ∀ i : Leaves (.split s P Q), (leafPrefix (.split s P Q) i).permute σ =
      leafPrefix (.split s P Q) i) : σ s = s := by
  classical
  by_contra hs
  let x : Box S := fun t => Stream'.const (decide (t = σ s))
  obtain ⟨i,hi,_⟩ := partition (.split s P Q) x
  let p := leafPrefix (.split s P Q) i
  have hp : p s = p (σ s) := by
    have he := congrArg (fun q : Prefix S => q (σ s)) (h i)
    simpa only [Prefix.permute_apply,Equiv.symm_apply_apply] using he
  have hn : 0 < (p s).length := List.length_pos_iff.mpr (split_prefix_nonempty s P Q i)
  have hm := (Prefix.mem_brick_iff_get p x).mp hi
  have hxs := hm s 0 hn
  have hxt := hm (σ s) 0 (by rw [← hp]; exact hn)
  have hh : (p (σ s))[0]'(by rw [← hp]; exact hn) = (p s)[0]'hn := by simp [hp]
  have he := hxs.trans (hxt.trans hh).symm
  simp [x,Stream'.get,Stream'.const,Ne.symm hs] at he

lemma coordinate_rigidity (σ : Equiv.Perm S) (P : Pattern S) :
    (∀ i : Leaves P, (leafPrefix P i).permute σ = leafPrefix P i) ↔
      ∀ s ∈ coordinates P, σ s = s := by
  classical
  induction P with
  | leaf => simp [coordinates,leafPrefix]
  | split s P Q ihP ihQ =>
    constructor
    · intro h
      have hs := root_fixed_of_prefixes_fixed σ s P Q h
      have hP : ∀ i : Leaves P, (leafPrefix P i).permute σ = leafPrefix P i := by
        intro i
        have he := h (.inl i)
        change ((Prefix.cut s false).append (leafPrefix P i)).permute σ =
          (Prefix.cut s false).append (leafPrefix P i) at he
        rw [Prefix.permute_append,Prefix.permute_cut,hs] at he
        exact Prefix.append_left_cancel _ he
      have hQ : ∀ i : Leaves Q, (leafPrefix Q i).permute σ = leafPrefix Q i := by
        intro i
        have he := h (.inr i)
        change ((Prefix.cut s true).append (leafPrefix Q i)).permute σ =
          (Prefix.cut s true).append (leafPrefix Q i) at he
        rw [Prefix.permute_append,Prefix.permute_cut,hs] at he
        exact Prefix.append_left_cancel _ he
      intro t ht
      simp only [coordinates,Finset.mem_insert,Finset.mem_union] at ht
      rcases ht with rfl | ht | ht
      · exact hs
      · exact ihP.mp hP t ht
      · exact ihQ.mp hQ t ht
    · intro h
      have hs : σ s = s := h s (by simp [coordinates])
      have hP := ihP.mpr (fun t ht => h t (by simp [coordinates,ht]))
      have hQ := ihQ.mpr (fun t ht => h t (by simp [coordinates,ht]))
      intro i
      cases i with
      | inl i => simp only [leafPrefix,Prefix.permute_append,Prefix.permute_cut,hs,hP]
      | inr i => simp only [leafPrefix,Prefix.permute_append,Prefix.permute_cut,hs,hQ]

end TwistedBrin.Pattern

namespace TwistedBrin.GermBrick
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma restriction_injective (h : LocalEmbedding ρ) :
    Function.Injective (fun p : Prefix S => mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p))) := by
  intro p q he
  have hr := congrArg (region ρ) he
  change Set.range (h ∘ p.chart) = Set.range (h ∘ q.chart) at hr
  rw [Set.range_comp,Set.range_comp] at hr
  exact Prefix.brick_injective ((Set.image_injective.mpr h.injective) hr)

end TwistedBrin.GermBrick

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace Basis

lemma twistPieces_expanded_fixed_iff (B : Basis ρ) (P : B → Pattern S) (a : B → A)
    (i : Σ b : B, Pattern.Leaves (P b)) :
    GermBrick.groupEquiv ρ (twistPiecesHom ρ B a)
      (GermBrick.mk ρ (expandedChart ρ B P i)) =
      GermBrick.mk ρ (expandedChart ρ B P i) ↔
    (Pattern.leafPrefix (P i.1) i.2).permute (ρ (a i.1)) = Pattern.leafPrefix (P i.1) i.2 := by
  rw [twistPieces_expanded_germ]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B i.1)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ _))) =
    GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B i.1)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ _))) ↔ _
  rw [Pattern.relabel_prefix]
  exact (GermBrick.restriction_injective ρ (chart ρ B i.1)).eq_iff

lemma Forest.twistPieces_mem_rigid_iff {B C : Basis ρ} (F : Forest ρ B C) (a : B → A) :
    twistPiecesHom ρ B a ∈ rigidStabilizer ρ C ↔
      ∀ b : B, a b ∈ pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b)) := by
  constructor
  · intro h b
    apply (Pattern.coordinate_rigidity (ρ (a b)) (F.pattern b)).mp
    intro i
    apply (twistPieces_expanded_fixed_iff ρ B F.pattern a ⟨b,i⟩).mp
    rw [F.chart_eq]
    exact h (F.leaves ⟨b,i⟩)
  · intro h c
    obtain ⟨⟨b,i⟩,rfl⟩ := F.leaves.surjective c
    rw [← F.chart_eq]
    apply (twistPieces_expanded_fixed_iff ρ B F.pattern a ⟨b,i⟩).mpr
    exact (Pattern.coordinate_rigidity (ρ (a b)) (F.pattern b)).mpr (h b) i

noncomputable def Forest.rigidPairHom {B C : Basis ρ} (F : Forest ρ B C) :
    (Π b : B, pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) →*
      ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) where
  toFun a := ⟨twistPiecesHom ρ B (fun b => (a b).val),
    twistPiecesHom_mem_rigidStabilizer ρ B _,
    (F.twistPieces_mem_rigid_iff ρ _).mpr (fun b => (a b).property)⟩
  map_one' := by
    apply Subtype.ext
    exact (twistPiecesHom ρ B).map_one
  map_mul' a c := by
    apply Subtype.ext
    exact (twistPiecesHom ρ B).map_mul _ _

noncomputable def Forest.rigidPairEquiv (hρ : Function.Injective ρ) {B C : Basis ρ}
    (F : Forest ρ B C) :
    (Π b : B, pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) ≃*
      ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) :=
  MulEquiv.ofBijective (F.rigidPairHom ρ) ⟨by
    intro a c he
    have hh := twistPiecesHom_injective ρ hρ B (congrArg Subtype.val he)
    funext b
    exact Subtype.ext (congrFun hh b),by
    rintro ⟨g,hgB,hgC⟩
    obtain ⟨a,rfl⟩ := exists_twistPiecesHom_of_mem ρ hgB
    have ha := (F.twistPieces_mem_rigid_iff ρ a).mp hgC
    exact ⟨fun b => ⟨a b,ha b⟩,rfl⟩⟩

end Basis
end TwistedBrin

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def pairStabilizer (B C : Basis ρ) : Subgroup (localGroup ρ) :=
  vertexStabilizer ρ B ⊓ vertexStabilizer ρ C

noncomputable def pairPermutationHom (B C : Basis ρ) :
    pairStabilizer ρ B C →* Equiv.Perm B × Equiv.Perm C :=
  ((vertexPermutationHom ρ B).comp
    (Subgroup.inclusion (show pairStabilizer ρ B C ≤ vertexStabilizer ρ B from inf_le_left))).prod
  ((vertexPermutationHom ρ C).comp
    (Subgroup.inclusion (show pairStabilizer ρ B C ≤ vertexStabilizer ρ C from inf_le_right)))

lemma mem_pairPermutationHom_ker (B C : Basis ρ) (g : pairStabilizer ρ B C) :
    g ∈ (pairPermutationHom ρ B C).ker ↔
      g.val ∈ rigidStabilizer ρ B ∧ g.val ∈ rigidStabilizer ρ C := by
  change ((vertexPermutationHom ρ B) ⟨g.val,g.property.1⟩,
    (vertexPermutationHom ρ C) ⟨g.val,g.property.2⟩) = (1,1) ↔ _
  rw [Prod.mk.injEq]
  exact and_congr (mem_vertexPermutationHom_ker ρ B ⟨g.val,g.property.1⟩)
    (mem_vertexPermutationHom_ker ρ C ⟨g.val,g.property.2⟩)

noncomputable def rigidPairToKernel (B C : Basis ρ) :
    ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) →*
      (pairPermutationHom ρ B C).ker where
  toFun g := ⟨⟨g.val,rigid_le_vertexStabilizer ρ B g.property.1,
    rigid_le_vertexStabilizer ρ C g.property.2⟩,
    (mem_pairPermutationHom_ker ρ B C _).mpr g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def rigidPairKernelEquiv (B C : Basis ρ) :
    ↥((rigidStabilizer ρ B ⊓ rigidStabilizer ρ C) : Subgroup (localGroup ρ)) ≃*
      (pairPermutationHom ρ B C).ker :=
  MulEquiv.ofBijective (rigidPairToKernel ρ B C) ⟨by
    intro g h he
    exact Subtype.ext (congrArg (fun k => k.val.val) he),by
    intro g
    exact ⟨⟨g.val.val,(mem_pairPermutationHom_ker ρ B C g.val).mp g.property⟩,rfl⟩⟩

noncomputable def Forest.pairKernelEquiv (hρ : Function.Injective ρ) {B C : Basis ρ}
    (F : Forest ρ B C) :
    (Π b : B, pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) ≃*
      (pairPermutationHom ρ B C).ker :=
  (F.rigidPairEquiv ρ hρ).trans (rigidPairKernelEquiv ρ B C)

end TwistedBrin.Basis

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma cut_append_cut (s t : S) (hs : s ≠ t) (a b : Bool) :
    (cut s a).append (cut t b) = (cut t b).append (cut s a) := by
  classical
  apply Prefix.ext
  intro r
  by_cases hr : r = s
  · subst r
    simp [hs]
  · by_cases ht : r = t
    · subst r
      simp [hr]
    · simp [hr,ht]

lemma cut_append_commute (s t : S) (hs : s ≠ t) (a b : Bool) (p : Prefix S) :
    (cut s a).append ((cut t b).append p) =
      (cut t b).append ((cut s a).append p) := by
  rw [← append_assoc,cut_append_cut s t hs,append_assoc]

end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

structure SplitView (P : Pattern S) (s : S) where
  left : Pattern S
  right : Pattern S
  leaves : Leaves (.split s left right) ≃ Leaves P
  prefix_eq : ∀ i, leafPrefix P (leaves i) = leafPrefix (.split s left right) i

noncomputable def SplitView.commute {P Q : Pattern S} {s t : S} (h : s ≠ t)
    (p : SplitView P s) (q : SplitView Q s) : SplitView (.split t P Q) s where
  left := .split t p.left q.left
  right := .split t p.right q.right
  leaves := shuffle.trans (Equiv.sumCongr p.leaves q.leaves)
  prefix_eq := by
    rintro ((i|i)|(i|i))
    · change (Prefix.cut t false).append (leafPrefix P (p.leaves (.inl i))) = _
      rw [p.prefix_eq (.inl i)]
      exact Prefix.cut_append_commute t s h.symm false false _
    · change (Prefix.cut t true).append (leafPrefix Q (q.leaves (.inl i))) = _
      rw [q.prefix_eq (.inl i)]
      exact Prefix.cut_append_commute t s h.symm true false _
    · change (Prefix.cut t false).append (leafPrefix P (p.leaves (.inr i))) = _
      rw [p.prefix_eq (.inr i)]
      exact Prefix.cut_append_commute t s h.symm false true _
    · change (Prefix.cut t true).append (leafPrefix Q (q.leaves (.inr i))) = _
      rw [q.prefix_eq (.inr i)]
      exact Prefix.cut_append_commute t s h.symm true true _

theorem splitView_exists (P : Pattern S) (s : S)
    (h : ∀ i : Leaves P, leafPrefix P i s ≠ []) : Nonempty (SplitView P s) := by
  induction P with
  | leaf => exact (h () rfl).elim
  | split t P Q ihP ihQ =>
    by_cases hst : s = t
    · subst s
      exact ⟨⟨P,Q,Equiv.refl _,fun _ => rfl⟩⟩
    · have hP : ∀ i : Leaves P, leafPrefix P i s ≠ [] := by
        intro i
        simpa [leafPrefix,Prefix.cut_apply,hst] using h (.inl i)
      have hQ : ∀ i : Leaves Q, leafPrefix Q i s ≠ [] := by
        intro i
        simpa [leafPrefix,Prefix.cut_apply,hst] using h (.inr i)
      obtain ⟨p⟩ := ihP hP
      obtain ⟨q⟩ := ihQ hQ
      exact ⟨p.commute hst q⟩

end TwistedBrin.Pattern

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPatternFactor
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
namespace TwistedBrin.Pattern
section
variable {S : Type u}

structure Factor (P Q : Pattern S) where
  remainder : Leaves P → Pattern S
  leaves : (Σ i : Leaves P, Leaves (remainder i)) ≃ Leaves Q
  prefix_eq : ∀ i, leafPrefix Q (leaves i) =
    (leafPrefix P i.1).append (leafPrefix (remainder i.1) i.2)

noncomputable def Factor.fromLeaf (P : Pattern S) : Factor .leaf P where
  remainder := fun _ => P
  leaves := {
    toFun := Sigma.snd
    invFun := fun i => ⟨(),i⟩
    left_inv := by rintro ⟨⟨⟩,i⟩; rfl
    right_inv := fun _ => rfl }
  prefix_eq := by rintro ⟨i,j⟩; exact (Prefix.empty_append _).symm

noncomputable def SplitView.uniformCons {P : Pattern S} {s : S} (p : SplitView P s)
    (L : List S) (f : Factor (uniform L) p.left) (g : Factor (uniform L) p.right) :
    Factor (uniform (s :: L)) P where
  remainder := Sum.elim f.remainder g.remainder
  leaves := (Equiv.sumSigmaDistrib (fun i => Leaves (Sum.elim f.remainder g.remainder i))).trans
    ((Equiv.sumCongr f.leaves g.leaves).trans p.leaves)
  prefix_eq := by
    rintro ⟨i,j⟩
    cases i with
    | inl i =>
      change leafPrefix P (p.leaves (.inl (f.leaves ⟨i,j⟩))) = _
      rw [p.prefix_eq (.inl (f.leaves ⟨i,j⟩))]
      change (Prefix.cut s false).append (leafPrefix p.left (f.leaves ⟨i,j⟩)) =
        ((Prefix.cut s false).append (leafPrefix (uniform L) i)).append _
      rw [f.prefix_eq ⟨i,j⟩,Prefix.append_assoc]
      rfl
    | inr i =>
      change leafPrefix P (p.leaves (.inr (g.leaves ⟨i,j⟩))) = _
      rw [p.prefix_eq (.inr (g.leaves ⟨i,j⟩))]
      change (Prefix.cut s true).append (leafPrefix p.right (g.leaves ⟨i,j⟩)) =
        ((Prefix.cut s true).append (leafPrefix (uniform L) i)).append _
      rw [g.prefix_eq ⟨i,j⟩,Prefix.append_assoc]
      rfl

theorem uniform_factor_exists (L : List S) (hn : L.Nodup) (P : Pattern S)
    (h : ∀ s ∈ L, ∀ i : Leaves P, leafPrefix P i s ≠ []) :
    Nonempty (Factor (uniform L) P) := by
  induction L generalizing P with
  | nil => exact ⟨Factor.fromLeaf P⟩
  | cons s L ih =>
    obtain ⟨hs,hL⟩ := List.nodup_cons.mp hn
    obtain ⟨p⟩ := splitView_exists P s (h s (by simp))
    have hl : ∀ t ∈ L, ∀ i : Leaves p.left, leafPrefix p.left i t ≠ [] := by
      intro t ht i
      have hts : t ≠ s := by rintro rfl; exact hs ht
      have hh := h t (List.mem_cons_of_mem s ht) (p.leaves (.inl i))
      rw [p.prefix_eq (.inl i)] at hh
      simpa [leafPrefix,hts] using hh
    have hr : ∀ t ∈ L, ∀ i : Leaves p.right, leafPrefix p.right i t ≠ [] := by
      intro t ht i
      have hts : t ≠ s := by rintro rfl; exact hs ht
      have hh := h t (List.mem_cons_of_mem s ht) (p.leaves (.inr i))
      rw [p.prefix_eq (.inr i)] at hh
      simpa [leafPrefix,hts] using hh
    obtain ⟨f⟩ := ih hL p.left hl
    obtain ⟨g⟩ := ih hL p.right hr
    exact ⟨p.uniformCons L f g⟩

noncomputable instance leavesNonempty (P : Pattern S) : Nonempty (Leaves P) := by
  obtain ⟨i,_,_⟩ := partition P (fun _ _ => false)
  exact ⟨i⟩

lemma mem_coordinates_of_prefix_nonempty (P : Pattern S) (i : Leaves P) (s : S)
    (h : leafPrefix P i s ≠ []) : s ∈ coordinates P := by
  classical
  induction P with
  | leaf => exact (h rfl).elim
  | split t P Q ihP ihQ =>
    by_cases hst : s = t
    · subst s; simp [coordinates]
    · cases i with
      | inl i =>
        have hh : leafPrefix P i s ≠ [] := by simpa [leafPrefix,hst] using h
        simp only [coordinates,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inl (ihP i hh))
      | inr i =>
        have hh : leafPrefix Q i s ≠ [] := by simpa [leafPrefix,hst] using h
        simp only [coordinates,Finset.mem_insert,Finset.mem_union]
        exact Or.inr (Or.inr (ihQ i hh))

lemma mem_firstCoordinates (P : Pattern S) (s : S) :
    s ∈ firstCoordinates P ↔ ∀ i : Leaves P, leafPrefix P i s ≠ [] := by
  classical
  rw [firstCoordinates,Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨mem_coordinates_of_prefix_nonempty P (Classical.arbitrary _) s (h _),h⟩

lemma firstCoordinates_nonempty {P : Pattern S} (h : P ≠ .leaf) :
    (firstCoordinates P).Nonempty := by
  cases P with
  | leaf => exact (h rfl).elim
  | split s P Q => exact ⟨s,(mem_firstCoordinates _ _).mpr (split_prefix_nonempty s P Q)⟩

lemma firstCoordinates_factor (P : Pattern S) (F : Finset S) (hF : F ⊆ firstCoordinates P) :
    Nonempty (Factor (uniform F.toList) P) := by
  classical
  apply uniform_factor_exists F.toList F.nodup_toList P
  intro s hs i
  exact (mem_firstCoordinates P s).mp (hF (Finset.mem_toList.mp hs)) i

end

variable {S : Type u}

lemma firstCoordinates_uniform [DecidableEq S] (L : List S) : firstCoordinates (uniform L) = L.toFinset := by
  classical
  ext s
  rw [mem_firstCoordinates,List.mem_toFinset]
  simp_rw [← List.length_pos_iff,uniform_length]
  simp only [List.count_pos_iff,forall_const]

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Forest.cutRefines_factor {B C : Basis ρ} (F : Forest ρ B C)
    (P : B → Pattern S) (f : ∀ b, Pattern.Factor (P b) (F.pattern b)) :
    CutRefines ρ (expand ρ B P) C := by
  apply cutRefines_ofChartPartition ρ (expandedChart ρ B P) (expanded_partition ρ B P)
    C (fun i => (f i.1).remainder i.2)
  rintro ⟨b,i⟩ j
  change GermBrick.mk ρ (LocalEmbedding.comp ρ
    (LocalEmbedding.comp ρ (chart ρ B b) (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P b) i)))
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix ((f b).remainder i) j))) ∈ C.pieces
  rw [LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,← (f b).prefix_eq ⟨i,j⟩]
  exact (F.chart_eq ⟨b,(f b).leaves ⟨i,j⟩⟩) ▸ (F.leaves ⟨b,(f b).leaves ⟨i,j⟩⟩).property

noncomputable def gridExpansion (B : Basis ρ) (K : B → Finset S) : Basis ρ :=
  expand ρ B (fun b => Pattern.uniform (K b).toList)

lemma cutRefines_gridExpansion (B : Basis ρ) (K : B → Finset S) :
    CutRefines ρ B (gridExpansion ρ B K) := ⟨Forest.expansion B _⟩

lemma Forest.gridExpansion_refines {B C : Basis ρ} (F : Forest ρ B C)
    (K : B → Finset S) (hK : ∀ b, K b ⊆ Pattern.firstCoordinates (F.pattern b)) :
    CutRefines ρ (gridExpansion ρ B K) C := by
  classical
  let f := fun b => Classical.choice (Pattern.firstCoordinates_factor (F.pattern b) (K b) (hK b))
  exact F.cutRefines_factor ρ (fun b => Pattern.uniform (K b).toList) f

noncomputable def Forest.firstGrid {B C : Basis ρ} (F : Forest ρ B C) : Basis ρ :=
  gridExpansion ρ B (fun b => Pattern.firstCoordinates (F.pattern b))

end TwistedBrin.Basis

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma firstCoordinates_eq_of_pieces_eq {P Q : Pattern S} (h : pieces P = pieces Q) :
    firstCoordinates P = firstCoordinates Q := by
  classical
  apply Finset.Subset.antisymm
  · intro s hs
    apply (mem_firstCoordinates Q s).mpr
    intro j
    have hj : leafPrefix Q j ∈ pieces P := by rw [h]; exact (mem_pieces Q _).mpr ⟨j,rfl⟩
    obtain ⟨i,hi⟩ := (mem_pieces P _).mp hj
    rw [← hi]
    exact (mem_firstCoordinates P s).mp hs i
  · intro s hs
    apply (mem_firstCoordinates P s).mpr
    intro i
    have hi : leafPrefix P i ∈ pieces Q := by rw [← h]; exact (mem_pieces P _).mpr ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := (mem_pieces Q _).mp hi
    rw [← hj]
    exact (mem_firstCoordinates Q s).mp hs j

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma gridExpansion_mono (B : Basis ρ) (K L : B → Finset S) (h : ∀ b, K b ⊆ L b) :
    CutRefines ρ (gridExpansion ρ B K) (gridExpansion ρ B L) := by
  classical
  apply (Forest.expansion B (fun b => Pattern.uniform (L b).toList)).gridExpansion_refines ρ K
  intro b
  change K b ⊆ Pattern.firstCoordinates (Pattern.uniform (L b).toList)
  simpa only [Pattern.firstCoordinates_uniform,Finset.toList_toFinset] using h b

end TwistedBrin.Basis

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma firstCoordinates_graft (P : Pattern S) (Q : Leaves P → Pattern S) :
    firstCoordinates P ⊆ firstCoordinates (graft P Q) := by
  intro s hs
  apply (mem_firstCoordinates _ _).mpr
  intro k
  obtain ⟨⟨i,j⟩,rfl⟩ := (graftLeaves P Q).surjective k
  rw [graft_prefix]
  intro he
  exact (mem_firstCoordinates P s).mp hs i ((List.append_eq_nil_iff.mp he).1)

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

@[simp] lemma gridExpansion_empty (B : Basis ρ) : gridExpansion ρ B (fun _ => ∅) = B := by
  simp only [gridExpansion,Finset.toList_empty,Pattern.uniform,expand_leaf]

noncomputable def firstCuts {B C : Basis ρ} (h : CutRefines ρ B C) : B → Finset S :=
  fun b => Pattern.firstCoordinates ((Classical.choice h).pattern b)

noncomputable def firstCore {B C : Basis ρ} (h : CutRefines ρ B C) : Basis ρ :=
  gridExpansion ρ B (firstCuts ρ h)

lemma firstCore_lower {B C : Basis ρ} (h : CutRefines ρ B C) : CutRefines ρ B (firstCore ρ h) :=
  cutRefines_gridExpansion ρ B _

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

structure CutInterval (B C : Basis ρ) where
  val : Basis ρ
  lower : CutRefines ρ B val
  upper : CutRefines ρ val C

namespace CutInterval
variable {ρ} {B C : Basis ρ}
@[ext] lemma ext {D E : CutInterval ρ B C} (h : D.val = E.val) : D = E := by
  cases D; cases E; simp_all
end CutInterval

def CutSelections {B C : Basis ρ} (h : CutRefines ρ B C) :=
  {K : B → Finset S // ∀ b, K b ⊆ firstCuts ρ h b}

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
instance instPartialOrder : PartialOrder (CutSelections ρ h) := inferInstanceAs
  (PartialOrder {K : B → Finset S // ∀ b, K b ⊆ firstCuts ρ h b})

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
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

noncomputable def FirstCut {B C : Basis ρ} (h : CutRefines ρ B C) :=
  (b : B) × {s : S // s ∈ firstCuts ρ h b}
noncomputable instance instFintypeFirstCut {B C : Basis ρ} (h : CutRefines ρ B C) : Fintype (FirstCut ρ h) := by
  classical
  unfold FirstCut
  infer_instance

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
noncomputable def selected (K : CutSelections ρ h) : Finset (FirstCut ρ h) := by
  classical
  exact Finset.univ.filter (fun x => x.2.val ∈ K.val x.1)
lemma mem_selected (K : CutSelections ρ h) (x : FirstCut ρ h) :
    x ∈ selected h K ↔ x.2.val ∈ K.val x.1 := by
  classical
  simp [selected]

noncomputable def fromSelected (T : Finset (FirstCut ρ h)) : CutSelections ρ h := by
  classical
  refine ⟨fun b => (@Finset.filter {s : S // s ∈ firstCuts ρ h b}
    (fun s => (⟨b,s⟩ : FirstCut ρ h) ∈ T)
    (fun s => @Finset.decidableMem (FirstCut ρ h)
      (fun x y => Classical.propDecidable (x = y)) ⟨b,s⟩ T)
    Finset.univ).map (Function.Embedding.subtype _), ?_⟩
  intro b s hs
  obtain ⟨s',_,rfl⟩ := Finset.mem_map.mp hs
  exact s'.property

lemma mem_fromSelected (T : Finset (FirstCut ρ h)) (b : B) (s : S) :
    s ∈ (fromSelected h T).val b ↔ ∃ hs : s ∈ firstCuts ρ h b,
      (⟨b,⟨s,hs⟩⟩ : FirstCut ρ h) ∈ T := by
  classical
  simp only [fromSelected, Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨s',hm,he⟩; subst s; exact ⟨s'.property,hm⟩
  · rintro ⟨hs,hm⟩; exact ⟨⟨s,hs⟩,hm,rfl⟩

lemma selected_fromSelected (T : Finset (FirstCut ρ h)) : selected h (fromSelected h T) = T := by
  classical
  ext x
  rw [mem_selected,mem_fromSelected]
  exact ⟨fun ⟨_,hh⟩ => hh,fun hh => ⟨x.2.property,hh⟩⟩

lemma fromSelected_selected (K : CutSelections ρ h) : fromSelected h (selected h K) = K := by
  apply Subtype.ext
  funext b
  apply Finset.ext
  intro s
  rw [mem_fromSelected]
  constructor
  · rintro ⟨hs,hm⟩
    exact (mem_selected h K ⟨b,⟨s,hs⟩⟩).mp hm
  · intro hm
    exact ⟨K.property b hm,(mem_selected h K _).mpr hm⟩

noncomputable def booleanEquiv : CutSelections ρ h ≃o Finset (FirstCut ρ h) where
  toFun := selected h
  invFun := fromSelected h
  left_inv := fromSelected_selected h
  right_inv := selected_fromSelected h
  map_rel_iff' := by
    intro K L
    change selected h K ⊆ selected h L ↔ ∀ b, K.val b ⊆ L.val b
    constructor
    · intro hh b s hs
      exact (mem_selected h L ⟨b,⟨s,K.property b hs⟩⟩).mp
        (hh ((mem_selected h K _).mpr hs))
    · intro hh x hx
      exact (mem_selected h L x).mpr (hh x.1 ((mem_selected h K x).mp hx))
end CutSelections

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

def ProperCutInterval (B C : Basis ρ) :=
  {D : CutInterval ρ B C // D.val ≠ B ∧ D.val ≠ C}

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
noncomputable def empty : CutSelections ρ h := ⟨fun _ => ∅,by simp⟩
noncomputable def full : CutSelections ρ h := ⟨firstCuts ρ h,fun _ _ hs => hs⟩
@[simp] lemma selected_empty : selected h (empty h) = ∅ := by
  classical
  ext x; simp [selected,empty]
@[simp] lemma selected_full : selected h (full h) = Finset.univ := by
  classical
  ext x; simp [selected,full]

end CutSelections
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfDirected
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

namespace Merge
variable {C : Basis ρ}
def endpoint (m : Merge ρ C) (q : Bool) : C := if q then m.second else m.first
end Merge

structure Matching (C : Basis ρ) (I : Type w) where
  edge : I → Merge ρ C
  endpoints_injective : Function.Injective (fun p : I × Bool => (edge p.1).endpoint p.2)

namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

def Present (B : Basis ρ) (N : Finset I) : Prop :=
  ∀ i ∈ N, ∀ q : Bool, ((M.edge i).endpoint q).val ∈ B.pieces

abbrev Rest (B : Basis ρ) (N : Finset I) :=
  {b : B // ∀ i ∈ N, ∀ q : Bool, b.val ≠ ((M.edge i).endpoint q).val}
abbrev Roots (B : Basis ρ) (N : Finset I) := N ⊕ M.Rest B N

noncomputable def rootChart (B : Basis ρ) (N : Finset I) : M.Roots B N → LocalEmbedding ρ
  | Sum.inl i => (M.edge i.val).joined
  | Sum.inr b => chart ρ B b.val

lemma endpoint_eq {i j : I} {p q : Bool}
    (he : ((M.edge i).endpoint p).val = ((M.edge j).endpoint q).val) : i = j ∧ p = q := by
  have hh := M.endpoints_injective (a₁ := (i,p)) (a₂ := (j,q)) (Subtype.ext he)
  exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩

lemma range_joined (i : I) : Set.range (M.edge i).joined =
    ⋃ q : Bool, GermBrick.region ρ ((M.edge i).endpoint q).val := by
  rw [(M.edge i).range_joined]
  ext x
  simp [Merge.endpoint]

lemma rootPartition (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    ∀ x : Box S, ∃! r : M.Roots B N, x ∈ Set.range (M.rootChart B N r) := by
  classical
  intro x
  obtain ⟨b,hb,hu⟩ := B.partition x
  have hleft (i : N) : x ∈ Set.range (M.rootChart B N (Sum.inl i)) ↔
      ∃ q : Bool, b.val = ((M.edge i.val).endpoint q).val := by
    change x ∈ Set.range (M.edge i.val).joined ↔ _
    rw [M.range_joined]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,congrArg Subtype.val ((hu ⟨_,h i.val i.property q⟩ hq).symm)⟩
    · rintro ⟨q,hq⟩
      exact ⟨q,hq ▸ hb⟩
  have hright (r : M.Rest B N) : x ∈ Set.range (M.rootChart B N (Sum.inr r)) ↔ r.val = b := by
    change x ∈ Set.range (chart ρ B r.val) ↔ _
    rw [chart_region]
    exact ⟨hu _,fun he => he.symm ▸ hb⟩
  by_cases ht : ∃ i : N, ∃ q : Bool, b.val = ((M.edge i.val).endpoint q).val
  · obtain ⟨i,q,hi⟩ := ht
    refine ⟨Sum.inl i,(hleft i).mpr ⟨q,hi⟩,?_⟩
    intro r hr
    cases r with
    | inl j =>
      obtain ⟨p,hj⟩ := (hleft j).mp hr
      exact congrArg Sum.inl (Subtype.ext (M.endpoint_eq (hj.symm.trans hi)).1)
    | inr r =>
      have he := (hright r).mp hr
      exact False.elim (r.property i.val i.property q ((congrArg Subtype.val he).trans hi))
  · have hr : ∀ i ∈ N, ∀ q : Bool, b.val ≠ ((M.edge i).endpoint q).val := by
      intro i hi q he
      exact ht ⟨⟨i,hi⟩,q,he⟩
    refine ⟨Sum.inr ⟨b,hr⟩,(hright _).mpr rfl,?_⟩
    intro r hh
    cases r with
    | inl i => exact False.elim (ht ⟨i,(hleft i).mp hh⟩)
    | inr r => exact congrArg Sum.inr (Subtype.ext ((hright r).mp hh))

noncomputable def contract (B : Basis ρ) (N : Finset I) (h : M.Present B N) : Basis ρ := by
  classical
  exact ofChartPartition ρ (M.rootChart B N) (M.rootPartition B N h)

lemma mem_contract (B : Basis ρ) (N : Finset I) (h : M.Present B N) (g : GermBrick ρ) :
    g ∈ (M.contract B N h).pieces ↔
      (∃ i ∈ N, g = GermBrick.mk ρ (M.edge i).joined) ∨
      (g ∈ B.pieces ∧ ∀ i ∈ N, ∀ q : Bool, g ≠ ((M.edge i).endpoint q).val) := by
  classical
  change g ∈ Finset.univ.image (fun r : M.Roots B N => GermBrick.mk ρ (M.rootChart B N r)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r,_,he⟩
    cases r with
    | inl i => exact Or.inl ⟨i.val,i.property,he.symm⟩
    | inr b =>
      have hb : b.val.val = g := (chart_germ ρ B b.val).symm.trans he
      exact Or.inr (hb ▸ ⟨b.val.property,b.property⟩)
  · rintro (⟨i,hi,he⟩ | ⟨hg,hr⟩)
    · exact ⟨Sum.inl ⟨i,hi⟩,Finset.mem_univ _,he.symm⟩
    · exact ⟨Sum.inr ⟨⟨g,hg⟩,hr⟩,Finset.mem_univ _,chart_germ ρ B ⟨g,hg⟩⟩

lemma contract_cutRefines (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    CutRefines ρ (M.contract B N h) B := by
  classical
  let P : M.Roots B N → Pattern S := Sum.elim (fun i => .split (M.edge i.val).coordinate .leaf .leaf)
    (fun _ => .leaf)
  apply cutRefines_ofChartPartition ρ (M.rootChart B N) (M.rootPartition B N h) B P
  intro r j
  cases r with
  | inl i =>
    cases j with
    | inl j =>
      simpa [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,(M.edge i.val).left_eq,
        Merge.endpoint] using h i.val i.property false
    | inr j =>
      simpa [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,(M.edge i.val).right_eq,
        Merge.endpoint] using h i.val i.property true
  | inr b =>
    simp [P,Pattern.leafPrefix,rootChart,LocalEmbedding.ofPrefix_empty,
      LocalEmbedding.comp_identity,chart_germ]

noncomputable def leafEquiv (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    (N × Bool) ⊕ M.Rest B N ≃ B := by
  classical
  let f : (N × Bool) ⊕ M.Rest B N → B := Sum.elim
    (fun p => ⟨((M.edge p.1.val).endpoint p.2).val,h _ p.1.property p.2⟩) (fun b => b.val)
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hh := M.endpoint_eq (i := i.1.val) (j := j.1.val) (p := i.2) (q := j.2) (congrArg (fun b : B => b.val) he)
        exact congrArg Sum.inl (Prod.ext (Subtype.ext hh.1) hh.2)
      | inr j => exact False.elim (j.property _ i.1.property i.2 (congrArg Subtype.val he).symm)
    | inr i =>
      cases j with
      | inl j => exact False.elim (i.property _ j.1.property j.2 (congrArg Subtype.val he))
      | inr j => exact congrArg Sum.inr (Subtype.ext he)
  · intro b
    by_cases ht : ∃ i : N, ∃ q : Bool, b.val = ((M.edge i.val).endpoint q).val
    · obtain ⟨i,q,he⟩ := ht
      exact ⟨Sum.inl (i,q),Subtype.ext he.symm⟩
    · have hr : ∀ i ∈ N, ∀ q : Bool, b.val ≠ ((M.edge i).endpoint q).val := by
        intro i hi q he
        exact ht ⟨⟨i,hi⟩,q,he⟩
      exact ⟨Sum.inr ⟨b,hr⟩,rfl⟩

lemma rank_contract (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    rank ρ (M.contract B N h) + N.card = rank ρ B := by
  classical
  rw [contract,rank_ofChartPartition,rank_eq_card]
  have hc := Fintype.card_congr (M.leafEquiv B N h)
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe] at hc ⊢
  omega

end Matching
end

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

lemma present_top (N : Finset I) : M.Present C N := fun i _ q => ((M.edge i).endpoint q).property

end Matching
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

namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

noncomputable def available (B : Basis ρ) (N : Finset I) : Finset I := by
  classical
  exact N.filter (fun i => ∀ q : Bool, ((M.edge i).endpoint q).val ∈ B.pieces)

lemma mem_available (B : Basis ρ) (N : Finset I) (i : I) :
    i ∈ M.available B N ↔ i ∈ N ∧ ∀ q : Bool, ((M.edge i).endpoint q).val ∈ B.pieces := by
  classical
  exact Finset.mem_filter

end Matching
end

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

structure CutDown (C : Basis ρ) where
  val : Basis ρ
  upper : CutRefines ρ val C
  ne : val ≠ C
namespace CutDown
variable {C : Basis ρ}
@[ext] lemma ext {B D : CutDown C} (h : B.val = D.val) : B = D := by
  cases B; cases D; simp_all

abbrev Near (C : Basis ρ) (m : ℕ) := {B : CutDown C // m ≤ rank ρ B.val}

end CutDown

namespace Matching
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)

structure Pair (m : ℕ) where
  base : CutDown.Near C m
  selected : Finset I
  nonempty : selected.Nonempty
  present : M.Present base.val.val selected

namespace Pair
variable {M} {m : ℕ}
omit [Fintype I] in
@[ext] lemma ext [Fintype I] {x y : M.Pair m} (h : x.base = y.base) (k : x.selected = y.selected) : x = y := by
  cases x; cases y; simp_all
end Pair

abbrev AvailableFaces (B : CutDown C) :=
  {N : OrderDual (Finset I) // N.Nonempty ∧ (OrderDual.ofDual N) ⊆ M.available B.val Finset.univ}

end Matching
end TwistedBrin.Basis

namespace TwistedBrin.Basis
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
                                                                       
structure CutBasis (ρ : A →* Equiv.Perm S) where
  val : Basis ρ
namespace CutBasis
@[ext] lemma ext {B C : CutBasis ρ} (h : B.val = C.val) : B = C := by
  cases B; cases C; simp_all
instance instNonempty : Nonempty (CutBasis ρ) := ⟨⟨trivial ρ⟩⟩
end CutBasis
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisCutBasis
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
namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
noncomputable instance instMulActionSubtypePermBoxMemSubgroupLocalGroup : MulAction (localGroup ρ) (CutBasis ρ) where
  smul g B := ⟨translate ρ g B.val⟩
  one_smul B := ext (translate_one ρ B.val)
  mul_smul g h B := ext (translate_mul ρ g h B.val)
@[simp] lemma smul_val (g : localGroup ρ) (B : CutBasis ρ) : (g • B).val = translate ρ g B.val := rfl
abbrev Sublevel (h : ℕ) := rankBelow (fun B : CutBasis ρ => rank ρ B.val) h
noncomputable instance instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel (h : ℕ) : MulAction (localGroup ρ) (Sublevel (ρ := ρ) h) where
  smul g B := ⟨g • B.val,by
    change rank ρ (translate ρ g B.val.val) ≤ h
    rw [rank_translate]
    exact B.property⟩
  one_smul B := Subtype.ext (one_smul _ B.val)
  mul_smul g k B := Subtype.ext (mul_smul g k B.val)
end TwistedBrin.Basis.CutBasis

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

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

abbrev Mon := FiniteAlgebraicEnvelopes.ZeroProduct.Mon K PartialAffine.monoid

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

def diagramsForward {Q W W' X Y Y' : Type} [Group Q] [Group W] [Group W']
    [MulAction Q X] [MulAction W Y] [MulAction W' Y']
    {K : Type} [CommRing K] {i : Q →* W} {t : X → Y}
    (D : StageGeometry.PairDiagrams K i t)
    (f : W →* W') (a : Y → Y') (h : ∀ w y, f w • a y = a (w • y)) :
    StageGeometry.PairDiagrams K (f.comp i) (a ∘ t) where
  map E := f.comp (D.map E)
  identity := congrArg (f.comp) D.identity
  commute E P hsum hEP hPE q u := (D.commute E P hsum hEP hPE q u).map f
  addition E P hsum hEP hPE q := by
    change f (D.map ⟨E.val + P.val, hsum⟩ q) = f (D.map E q) * f (D.map P q)
    rw [D.addition E P hsum hEP hPE, map_mul]
  fixed E q x hx := by
    change f (D.map E q) • a (t x) = a (t x)
    rw [h, D.fixed E q x hx]

def diagramsBackward {Q' Q W X' X Y : Type} [Group Q'] [Group Q] [Group W]
    [MulAction Q' X'] [MulAction Q X] [MulAction W Y]
    {K : Type} [CommRing K] {i : Q →* W} {t : X → Y}
    (D : StageGeometry.PairDiagrams K i t)
    (f : Q' →* Q) (a : X' → X) (h : ∀ q x, f q • a x = a (q • x)) :
    StageGeometry.PairDiagrams K (i.comp f) (t ∘ a) where
  map E := (D.map E).comp f
  identity := congrArg (fun j => j.comp f) D.identity
  commute E P hsum hEP hPE q u := D.commute E P hsum hEP hPE (f q) (f u)
  addition E P hsum hEP hPE q := D.addition E P hsum hEP hPE (f q)
  fixed E q x hx := D.fixed E (f q) (a x) (by rw [h, hx])

namespace Saturation
variable {W X Y : Type} [Group W] [MulAction W Y] (t : X → Y)

def diagrams {Q : Type} [Group Q] [MulAction Q X]
    {K : Type} [CommRing K] {i : Q →* W} (D : StageGeometry.PairDiagrams K i t) :
    StageGeometry.PairDiagrams K i (point (W := W) t) where
  map := D.map
  identity := D.identity
  commute := D.commute
  addition := D.addition
  fixed E q x hx := Subtype.ext (D.fixed E q x hx)
end Saturation

end SourceEnlargement
end

end OAI
end


