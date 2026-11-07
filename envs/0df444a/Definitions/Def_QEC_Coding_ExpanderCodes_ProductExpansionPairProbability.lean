-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
-- name    : QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:41:17.760347+00:00
-- url     : https://prove2.me/theorems/b57c218c-7925-4d13-9818-361bb5426965
-- title:
--   Product Expansion Pair Probability
-- statement:
--   Definitions and structural lemmas for Product Expansion Pair Probability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionPairProbability.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
namespace QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
abbrev LocalMatrixPair := Matrix R W F × Matrix R' W F
def badFirstKernelPairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0}
def badFirstImagePairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ a : Word F R,
      a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d}
def badSecondKernelPairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0}
def badSecondImagePairs (d : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ a : Word F R',
      a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d}
def badForwardRectanglePairs (s m k : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.2 * x).rank ∧
        ProductKernel p.1 (generatorImageParityCheck p.2) x}
def badReverseRectanglePairs (s m k : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    ∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.1 * x).rank ∧
        ProductKernel p.2 (generatorImageParityCheck p.1) x}
noncomputable instance badFirstKernelPairsFintype (d : Nat) :
    Fintype (badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badFirstKernelPairs LocalMatrixPair
  infer_instance
noncomputable instance badFirstImagePairsFintype (d : Nat) :
    Fintype (badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badFirstImagePairs LocalMatrixPair
  infer_instance
noncomputable instance badSecondKernelPairsFintype (d : Nat) :
    Fintype (badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badSecondKernelPairs LocalMatrixPair
  infer_instance
noncomputable instance badSecondImagePairsFintype (d : Nat) :
    Fintype (badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d) := by
  classical
  unfold badSecondImagePairs LocalMatrixPair
  infer_instance
noncomputable instance badForwardRectanglePairsFintype (s m k : Nat) :
    Fintype (badForwardRectanglePairs
      (F := F) (W := W) (R := R) (R' := R') s m k) := by
  classical
  unfold badForwardRectanglePairs LocalMatrixPair
  infer_instance
noncomputable instance badReverseRectanglePairsFintype (s m k : Nat) :
    Fintype (badReverseRectanglePairs
      (F := F) (W := W) (R := R) (R' := R') s m k) := by
  classical
  unfold badReverseRectanglePairs LocalMatrixPair
  infer_instance
def badFirstKernelPairsEncoding (d : Nat) :
    badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d →
      badChecksForDistance (F := F) (W := W) (R := R) d × Matrix R' W F :=
  fun p => (⟨p.1.1, p.2⟩, p.1.2)
def badFirstImagePairsEncoding (d : Nat) :
    badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d →
      badGeneratorsForDistance (F := F) (W := W) (R := R) d × Matrix R' W F :=
  fun p => (⟨p.1.1, p.2⟩, p.1.2)
def badSecondKernelPairsEncoding (d : Nat) :
    badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d →
      Matrix R W F × badChecksForDistance (F := F) (W := W) (R := R') d :=
  fun p => (p.1.1, ⟨p.1.2, p.2⟩)
def badSecondImagePairsEncoding (d : Nat) :
    badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d →
      Matrix R W F × badGeneratorsForDistance (F := F) (W := W) (R := R') d :=
  fun p => (p.1.1, ⟨p.1.2, p.2⟩)
noncomputable def badForwardRectanglePairsEquivSigma (s m k : Nat) :
    badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k ≃
      Σ g' : Matrix R' W F,
        badChecksAllExactRectangles (R := R)
          (generatorImageParityCheck g') s m k where
  toFun p := ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
  invFun z := ⟨(z.2.1, z.1), z.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv z := by cases z; rfl
noncomputable def badReverseRectanglePairsEquivSigma (s m k : Nat) :
    badReverseRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k ≃
      Σ h : Matrix R W F,
        badChecksAllExactRectangles (R := R')
          (generatorImageParityCheck h) s m k where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun z := ⟨(z.1, z.2.1), z.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv z := by cases z; rfl
def badBidirectionalLocalPairs (d s m k : Nat) :=
  {p : LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') //
    (∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.1.mulVec c = 0) ∨
    (∃ a : Word F R,
      a ≠ 0 ∧ HammingWeight (p.1.transpose.mulVec a) < d) ∨
    (∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.2.mulVec c = 0) ∨
    (∃ a : Word F R',
      a ≠ 0 ∧ HammingWeight (p.2.transpose.mulVec a) < d) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.2 * x).rank ∧
        ProductKernel p.1 (generatorImageParityCheck p.2) x) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (generatorImageParityCheck p.1 * x).rank ∧
        ProductKernel p.2 (generatorImageParityCheck p.1) x)}
noncomputable instance badBidirectionalLocalPairsFintype
    (d s m k : Nat) :
    Fintype (badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) := by
  classical
  unfold badBidirectionalLocalPairs LocalMatrixPair
  infer_instance
noncomputable def badBidirectionalLocalPairsEncoding
    (d s m k : Nat)
    (p : badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) :
    badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badForwardRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k ⊕
        badReverseRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k)))) := by
  classical
  by_cases h₁ : ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ p.1.1.mulVec c = 0
  · exact Sum.inl ⟨p.1, h₁⟩
  · by_cases h₂ : ∃ a : Word F R,
        a ≠ 0 ∧ HammingWeight (p.1.1.transpose.mulVec a) < d
    · exact Sum.inr (Sum.inl ⟨p.1, h₂⟩)
    · by_cases h₃ : ∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ p.1.2.mulVec c = 0
      · exact Sum.inr (Sum.inr (Sum.inl ⟨p.1, h₃⟩))
      · by_cases h₄ : ∃ a : Word F R',
            a ≠ 0 ∧ HammingWeight (p.1.2.transpose.mulVec a) < d
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨p.1, h₄⟩)))
        · by_cases h₅ : ∃ A B : Finset W,
              A.card = Fintype.card W - m ∧
              B.card = Fintype.card W - m ∧
              ∃ x : Matrix W W F,
                restrictedWeight x A B < s ∧
                k ≤ (generatorImageParityCheck p.1.2 * x).rank ∧
                ProductKernel p.1.1
                  (generatorImageParityCheck p.1.2) x
          · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
              (Sum.inl ⟨p.1, h₅⟩))))
          · have hRest₂ := p.2.resolve_left h₁
            have hRest₃ := hRest₂.resolve_left h₂
            have hRest₄ := hRest₃.resolve_left h₃
            have hRest₅ := hRest₄.resolve_left h₄
            have h₆ := hRest₅.resolve_left h₅
            exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
              (Sum.inr ⟨p.1, h₆⟩))))
def badBidirectionalLocalPairsSumVal {d s m k : Nat} :
    badFirstKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badFirstImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondKernelPairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badSecondImagePairs (F := F) (W := W) (R := R) (R' := R') d ⊕
      (badForwardRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k ⊕
        badReverseRectanglePairs
          (F := F) (W := W) (R := R) (R' := R') s m k)))) →
      LocalMatrixPair (F := F) (W := W) (R := R) (R' := R') :=
  Sum.elim Subtype.val
    (Sum.elim Subtype.val
      (Sum.elim Subtype.val
        (Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val))))
end QEC.Coding.ProductExpansion


