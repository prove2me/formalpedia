-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
-- name    : QEC_Coding_ExpanderCodes_ProductExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:23:00.585214+00:00
-- url     : https://prove2.me/theorems/3762a832-1352-4f1a-8215-ac75531780db
-- title:
--   Product Expansion
-- statement:
--   Definitions and structural lemmas for Product Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
set_option autoImplicit false
namespace QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
noncomputable def parityCheckCode (h : Matrix R W F) : LinearCode F W := by
  classical
  exact ⟨LinearMap.ker (Matrix.toLin' h)⟩
def ProductKernel (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Matrix W W F) : Prop :=
  h' * x * h.transpose = 0
def restrictionLinearMap (A : Finset W) :
    Word F W →ₗ[F] ({i : W // i ∈ A} → F) where
  toFun x i := x i.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
noncomputable def codeRestriction (h : Matrix R W F) (A : Finset W) :
    (parityCheckCode h).carrier →ₗ[F] ({i : W // i ∈ A} → F) :=
  (restrictionLinearMap A).comp (parityCheckCode h).carrier.subtype
def row (x : Matrix W W F) (i : W) : Word F W := x i
def column (x : Matrix W W F) (j : W) : Word F W := fun i => x i j
def mapRows {I : Type v} (T : Word F W →ₗ[F] Word F W)
    (x : Matrix I W F) : Matrix I W F :=
  fun i => T (x i)
def IsDeltaMinimal (h : Matrix R W F) (h' : Matrix R' W F)
    (delta : ℝ) (x : Matrix W W F) : Prop :=
  (∀ i : W, ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
    (HammingWeight (row x i) : ℝ) ≤ HammingWeight (row x i + c) + delta) ∧
  (∀ j : W, ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
    (HammingWeight (column x j) : ℝ) ≤ HammingWeight (column x j + c) + delta)
def restrictedWeight (x : Matrix W W F) (A B : Finset W) : Nat :=
  ∑ i ∈ A, ∑ j ∈ B, if x i j = 0 then 0 else 1
def ProductExpanding (h : Matrix R W F) (h' : Matrix R' W F)
    (s m : Nat) (beta : ℝ) : Prop :=
  ∀ x : Matrix W W F, ProductKernel h h' x → x ≠ 0 →
    IsDeltaMinimal h h' (beta * Fintype.card W) x →
      ∀ A B : Finset W,
        Fintype.card W - m ≤ A.card → Fintype.card W - m ≤ B.card →
          s ≤ restrictedWeight x A B
def nonzeroRows (x : Matrix W W F) : Finset W :=
  Finset.univ.filter (fun i => row x i ≠ 0)
def nonzeroColumns (x : Matrix W W F) : Finset W :=
  Finset.univ.filter (fun j => column x j ≠ 0)
noncomputable def nonzeroRowsOnColumns (x : Matrix W W F) (B : Finset W) : Finset W := by
  classical
  exact Finset.univ.filter (fun i => ∃ j ∈ B, x i j ≠ 0)
noncomputable def nonzeroColumnsOnRows (x : Matrix W W F) (B : Finset W) : Finset W := by
  classical
  exact Finset.univ.filter (fun j => ∃ i ∈ B, x i j ≠ 0)
noncomputable def generatorSupport (C : Finset (Word F W)) : Finset W := by
  classical
  exact C.biUnion hammingSupport
noncomputable def supportedWords (S : Finset W) : Submodule F (Word F W) := by
  classical
  exact LinearMap.ker (restrictionLinearMap (Finset.univ \ S))
noncomputable def syndromeSpan (h' : Matrix R' W F)
    (C : Finset (Word F W)) : Submodule F (R' → F) :=
  Submodule.span F ((fun y : Word F W => h'.mulVec y) '' (C : Set (Word F W)))
def restrictedHammingWeight (A : Finset W) (y : Word F W) : Nat :=
  ∑ i ∈ A, if y i = 0 then 0 else 1
def generatorRestrictedWeight (A : Finset W) (C : Finset (Word F W)) : Nat :=
  ∑ y ∈ C, restrictedHammingWeight A y
noncomputable def lightGenerators (A : Finset W)
    (C : Finset (Word F W)) (d : Nat) : Finset (Word F W) := by
  classical
  exact C.filter (fun y => 6 * C.card * restrictedHammingWeight A y < d)
noncomputable def generatorSupportOn (A : Finset W) (C : Finset (Word F W)) :
    Finset W := by
  classical
  exact generatorSupport C ∩ A
noncomputable def columnsWithSyndromeInSpan
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W)) : Finset W := by
  classical
  exact Finset.univ.filter (fun j =>
    h'.mulVec (column x j) ∈ syndromeSpan h' C)
noncomputable def columnsOutsideSyndromeSpan
    (h' : Matrix R' W F) (x : Matrix W W F)
    (C : Finset (Word F W)) : Finset W := by
  classical
  exact Finset.univ \ columnsWithSyndromeInSpan h' x C
end QEC.Coding.ProductExpansion


