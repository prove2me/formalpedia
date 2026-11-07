-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
-- name    : QEC_Coding_ExpanderCodes_ProductExpansionProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:33:01.257768+00:00
-- url     : https://prove2.me/theorems/74982958-c9a6-4f69-84bd-11ab07f2017d
-- title:
--   Product Expansion Probability
-- statement:
--   Definitions and structural lemmas for Product Expansion Probability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
def rectangleSupport (x : Matrix W W F) (A B : Finset W) : Finset (W × W) :=
  (A ×ˢ B).filter (fun p => x p.1 p.2 ≠ 0)
omit [Fintype F] [Fintype W] [Fintype R] [Fintype R'] in
/-- The rectangle support has exactly the restricted Hamming weight. -/
theorem card_rectangleSupport
    (x : Matrix W W F) (A B : Finset W) :
    (rectangleSupport x A B).card = restrictedWeight x A B := by
  classical
  calc
    (rectangleSupport x A B).card =
        ∑ p ∈ A ×ˢ B, if x p.1 p.2 ≠ 0 then 1 else 0 := by
          rw [rectangleSupport, Finset.card_filter]
    _ = ∑ i ∈ A, ∑ j ∈ B, if x i j = 0 then 0 else 1 := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : x i j = 0 <;> simp [h]
    _ = restrictedWeight x A B := rfl
noncomputable def sparseRectangleEncoding
    [DecidableEq W]
    (A B : Finset W) (s : Nat)
    (x : {x : Matrix W W F // restrictedWeight x A B < s}) :
    Σ S : {S : Finset (W × W) // S ⊆ A ×ˢ B ∧ S.card < s},
      (((Finset.univ \ (A ×ˢ B) : Finset (W × W)) → F) × (S.1 → F)) := by
  classical
  let S := rectangleSupport x.1 A B
  have hSSubset : S ⊆ A ×ˢ B := Finset.filter_subset _ _
  have hSCard : S.card < s := by
    rw [card_rectangleSupport]
    exact x.2
  exact ⟨⟨S, hSSubset, hSCard⟩,
    ⟨(fun p => x.1 p.1.1 p.1.2), fun p => x.1 p.1.1 p.1.2⟩⟩
noncomputable def smallSubsetsEquivSigmaPowersetCard
    {α : Type*} (U : Finset α) (s : Nat) :
    {S : Finset α // S ⊆ U ∧ S.card < s} ≃
      Σ t : Fin s, U.powersetCard t.1 := by
  classical
  refine
    { toFun := fun S =>
        ⟨⟨S.1.card, S.2.2⟩,
          ⟨S.1, Finset.mem_powersetCard.mpr ⟨S.2.1, rfl⟩⟩⟩
      invFun := fun z =>
        ⟨z.2.1, (Finset.mem_powersetCard.mp z.2.2).1,
          by
            rw [(Finset.mem_powersetCard.mp z.2.2).2]
            exact z.1.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro S
    apply Subtype.ext
    rfl
  · rintro ⟨t, S⟩
    have hcard : S.1.card = t.1 := (Finset.mem_powersetCard.mp S.2).2
    have ht : (⟨S.1.card,
        by rw [hcard]; exact t.2⟩ : Fin s) = t := by
      apply Fin.ext
      exact hcard
    apply Sigma.ext ht
    apply (Subtype.heq_iff_coe_eq (fun X => by
      change X ∈ U.powersetCard S.1.card ↔ X ∈ U.powersetCard t.1
      rw [hcard])).mpr
    rfl
noncomputable def sparseWordEncoding
    [DecidableEq W] (d : Nat)
    (c : {c : Word F W // HammingWeight c < d}) :
    Σ S : {S : Finset W // S ⊆ Finset.univ ∧ S.card < d}, S.1 → F := by
  classical
  let S := hammingSupport c.1
  have hS : S.card < d := c.2
  exact ⟨⟨S, Finset.subset_univ S, hS⟩, fun i => c.1 i.1⟩
def singleRowMatrix (c : Word F W) : Matrix (ULift.{v} Unit) W F := fun _ j => c j
noncomputable def leftProductKernelEquivRows
    (M : Matrix R' W F) :
    {h : Matrix R W F // M * h.transpose = 0} ≃
      (R → LinearMap.ker M.mulVecLin) := by
  classical
  refine
    { toFun := fun h r => ⟨h.1 r, ?_⟩
      invFun := fun rows => ⟨(fun r w => (rows r).1 w), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change M.mulVec (h.1 r) = 0
    ext i
    have hEntry := congrArg (fun N : Matrix R' R F => N i r) h.2
    simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct] using hEntry
  · ext i r
    have hRow : M.mulVec ((rows r).1) = 0 := (rows r).2
    have hEntry := congrFun hRow i
    change (∑ j : W, M i j * (rows r).1 j) = 0
    simpa [Matrix.mulVec, dotProduct] using hEntry
  · intro h
    apply Subtype.ext
    ext r w
    rfl
  · intro rows
    funext r
    apply Subtype.ext
    funext w
    rfl
def badChecksForDistance (d : Nat) :=
  {h : Matrix R W F // ∃ c : Word F W,
    c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0}
noncomputable instance badChecksForDistanceFintype (d : Nat) :
    Fintype (badChecksForDistance (F := F) (W := W) (R := R) d) := by
  classical
  unfold badChecksForDistance
  infer_instance
noncomputable def badChecksForDistanceEncoding (d : Nat)
    (h : badChecksForDistance (F := F) (W := W) (R := R) d) :
    Σ c : {c : Word F W // c ≠ 0 ∧ HammingWeight c < d},
      {g : Matrix R W F // g.mulVec c.1 = 0} := by
  let c := Classical.choose h.2
  have hc := Classical.choose_spec h.2
  exact ⟨⟨c, hc.1, hc.2.1⟩, ⟨h.1, hc.2.2⟩⟩
noncomputable def generatorFiberBase
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) : Matrix W R F := by
  classical
  have hExists : ∃ i, a i ≠ 0 := by
    by_contra hNo
    push Not at hNo
    apply ha
    funext i
    exact hNo i
  let i₀ := Classical.choose hExists
  exact fun j i => if i = i₀ then (a i₀)⁻¹ * y j else 0
omit [Fintype F] [Fintype W] [Fintype R'] in
/-- The chosen affine-fiber base maps to its prescribed target word. -/
theorem generatorFiberBase_mulVec
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) :
    (generatorFiberBase a ha y).mulVec a = y := by
  classical
  have hExists : ∃ i, a i ≠ 0 := by
    by_contra hNo
    push Not at hNo
    apply ha
    funext i
    exact hNo i
  let i₀ := Classical.choose hExists
  have hi₀ : a i₀ ≠ 0 := Classical.choose_spec hExists
  funext j
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i₀]
  · simp only [generatorFiberBase, i₀, if_pos, mul_assoc]
    rw [mul_comm (y j) (a i₀), ← mul_assoc, inv_mul_cancel₀ hi₀, one_mul]
  · intro i hi hne
    simp [generatorFiberBase, i₀, hne]
  · simp
noncomputable def generatorFiberEquivAnnihilator
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) :
    {g : Matrix R W F // g.transpose.mulVec a = y} ≃
      {h : Matrix W R F // h.mulVec a = 0} where
  toFun g := ⟨g.1.transpose - generatorFiberBase a ha y, by
    rw [Matrix.sub_mulVec, g.2, generatorFiberBase_mulVec a ha y, sub_self]⟩
  invFun h := ⟨(h.1 + generatorFiberBase a ha y).transpose, by
    rw [Matrix.transpose_transpose, Matrix.add_mulVec, h.2,
      generatorFiberBase_mulVec a ha y, zero_add]⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv h := by
    apply Subtype.ext
    simp
def badGeneratorsForDistance (d : Nat) :=
  {g : Matrix R W F // ∃ a : Word F R,
    a ≠ 0 ∧ HammingWeight (g.transpose.mulVec a) < d}
noncomputable instance badGeneratorsForDistanceFintype (d : Nat) :
    Fintype (badGeneratorsForDistance (F := F) (W := W) (R := R) d) := by
  classical
  unfold badGeneratorsForDistance
  infer_instance
noncomputable def badGeneratorsForDistanceEncoding (d : Nat)
    (g : badGeneratorsForDistance (F := F) (W := W) (R := R) d) :
    Σ a : {a : Word F R // a ≠ 0},
      Σ y : {y : Word F W // HammingWeight y < d},
        {f : Matrix R W F // f.transpose.mulVec a.1 = y.1} := by
  let a := Classical.choose g.2
  have ha := Classical.choose_spec g.2
  exact ⟨⟨a, ha.1⟩, ⟨⟨g.1.transpose.mulVec a, ha.2⟩, ⟨g.1, rfl⟩⟩⟩
noncomputable def generatorImage (g : Matrix R W F) :
    Submodule F (Word F W) := by
  classical
  exact LinearMap.range (Matrix.toLin' g.transpose)
noncomputable def generatorImageComplement (g : Matrix R W F) :
    Submodule F (Word F W) :=
  Classical.choose (Submodule.exists_isCompl (generatorImage g))
omit [Fintype F] [DecidableEq F] [Fintype W] [Fintype R'] in
/-- The chosen complement really is complementary to the generator image. -/
theorem generatorImageComplement_isCompl (g : Matrix R W F) :
    IsCompl (generatorImageComplement g) (generatorImage g) :=
  (Classical.choose_spec
    (Submodule.exists_isCompl (generatorImage g))).symm
noncomputable def generatorImageParityCheck (g : Matrix R W F) : Matrix W W F := by
  classical
  exact LinearMap.toMatrix'
    ((generatorImageComplement g).projection (generatorImage g)
      (generatorImageComplement_isCompl g))
def badChecksForRectangle
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :=
  {h : Matrix R W F // ∃ x : Matrix W W F,
    restrictedWeight x A B < s ∧ k ≤ (h' * x).rank ∧ ProductKernel h h' x}
noncomputable instance badChecksForRectangleFintype
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat) :
    Fintype (badChecksForRectangle (R := R) h' A B s k) := by
  classical
  unfold badChecksForRectangle
  infer_instance
noncomputable def badChecksForRectangleEncoding
    (h' : Matrix R' W F) (A B : Finset W) (s k : Nat)
    (h : badChecksForRectangle (R := R) h' A B s k) :
    Σ x : {x : Matrix W W F //
        restrictedWeight x A B < s ∧ k ≤ (h' * x).rank},
      {g : Matrix R W F // ProductKernel g h' x.1} := by
  let x := Classical.choose h.2
  have hx := Classical.choose_spec h.2
  exact ⟨⟨x, hx.1, hx.2.1⟩, ⟨h.1, hx.2.2⟩⟩
def exactRectangleSides (W : Type v) [Fintype W] (m : Nat) :=
  {A : Finset W // A.card = Fintype.card W - m}
noncomputable def exactRectangleSidesEquivPowersetCard
    (W : Type v) [Fintype W] (m : Nat) :
    exactRectangleSides W m ≃
      (Finset.univ : Finset W).powersetCard (Fintype.card W - m) := by
  classical
  refine
    { toFun := fun A =>
        ⟨A.1, Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ A.1, A.2⟩⟩
      invFun := fun A =>
        ⟨A.1, (Finset.mem_powersetCard.mp A.2).2⟩
      left_inv := fun A => by apply Subtype.ext; rfl
      right_inv := fun A => by apply Subtype.ext; rfl }
noncomputable instance exactRectangleSidesFintype
    (W : Type v) [Fintype W] (m : Nat) : Fintype (exactRectangleSides W m) := by
  classical
  exact Fintype.ofEquiv
    ((Finset.univ : Finset W).powersetCard (Fintype.card W - m))
    (exactRectangleSidesEquivPowersetCard W m).symm
def badChecksAllExactRectangles
    (h' : Matrix R' W F) (s m k : Nat) :=
  {h : Matrix R W F // ∃ A B : Finset W,
    A.card = Fintype.card W - m ∧
    B.card = Fintype.card W - m ∧
    ∃ x : Matrix W W F,
      restrictedWeight x A B < s ∧
      k ≤ (h' * x).rank ∧ ProductKernel h h' x}
noncomputable instance badChecksAllExactRectanglesFintype
    (h' : Matrix R' W F) (s m k : Nat) :
    Fintype (badChecksAllExactRectangles (R := R) h' s m k) := by
  classical
  unfold badChecksAllExactRectangles
  infer_instance
noncomputable def badChecksAllExactRectanglesEncoding
    (h' : Matrix R' W F) (s m k : Nat)
    (h : badChecksAllExactRectangles (R := R) h' s m k) :
    Σ A : exactRectangleSides W m,
      Σ B : exactRectangleSides W m,
        badChecksForRectangle (R := R) h' A.1 B.1 s k := by
  let A := Classical.choose h.2
  let hA := Classical.choose_spec h.2
  let B := Classical.choose hA
  let hB := Classical.choose_spec hA
  exact ⟨⟨A, hB.1⟩, ⟨⟨B, hB.2.1⟩, ⟨h.1, hB.2.2⟩⟩⟩
def badChecksDistanceOrRectangles
    (h' : Matrix R' W F) (d s m k : Nat) :=
  {h : Matrix R W F //
    (∃ c : Word F W, c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (h' * x).rank ∧ ProductKernel h h' x)}
noncomputable instance badChecksDistanceOrRectanglesFintype
    (h' : Matrix R' W F) (d s m k : Nat) :
    Fintype (badChecksDistanceOrRectangles (R := R) h' d s m k) := by
  classical
  unfold badChecksDistanceOrRectangles
  infer_instance
noncomputable def badChecksDistanceOrRectanglesEncoding
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceOrRectangles (R := R) h' d s m k) :
    badChecksForDistance (F := F) (W := W) (R := R) d ⊕
      badChecksAllExactRectangles (R := R) h' s m k := by
  classical
  by_cases hd : ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ h.1.mulVec c = 0
  · exact Sum.inl ⟨h.1, hd⟩
  · exact Sum.inr ⟨h.1, h.2.resolve_left hd⟩
def badChecksDistanceImageOrRectangles
    (h' : Matrix R' W F) (d s m k : Nat) :=
  {h : Matrix R W F //
    (∃ c : Word F W, c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
    (∃ a : Word F R,
      a ≠ 0 ∧ HammingWeight (h.transpose.mulVec a) < d) ∨
    (∃ A B : Finset W,
      A.card = Fintype.card W - m ∧
      B.card = Fintype.card W - m ∧
      ∃ x : Matrix W W F,
        restrictedWeight x A B < s ∧
        k ≤ (h' * x).rank ∧ ProductKernel h h' x)}
noncomputable instance badChecksDistanceImageOrRectanglesFintype
    (h' : Matrix R' W F) (d s m k : Nat) :
    Fintype (badChecksDistanceImageOrRectangles (R := R) h' d s m k) := by
  classical
  unfold badChecksDistanceImageOrRectangles
  infer_instance
noncomputable def badChecksDistanceImageOrRectanglesEncoding
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceImageOrRectangles (R := R) h' d s m k) :
    badChecksForDistance (F := F) (W := W) (R := R) d ⊕
      (badGeneratorsForDistance (F := F) (W := W) (R := R) d ⊕
        badChecksAllExactRectangles (R := R) h' s m k) := by
  classical
  by_cases hd : ∃ c : Word F W,
      c ≠ 0 ∧ HammingWeight c < d ∧ h.1.mulVec c = 0
  · exact Sum.inl ⟨h.1, hd⟩
  · by_cases hi : ∃ a : Word F R,
        a ≠ 0 ∧ HammingWeight (h.1.transpose.mulVec a) < d
    · exact Sum.inr (Sum.inl ⟨h.1, hi⟩)
    · exact Sum.inr (Sum.inr ⟨h.1,
        (h.2.resolve_left hd).resolve_left hi⟩)
end QEC.Coding.ProductExpansion


