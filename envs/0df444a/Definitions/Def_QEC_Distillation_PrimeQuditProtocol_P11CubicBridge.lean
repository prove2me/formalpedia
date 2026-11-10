-- Prove2me | Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
-- name    : QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T13:01:07.488216+00:00
-- url     : https://prove2.me/theorems/382c8a0a-f484-415b-a67d-b5f7f1dd959f
-- title:
--   P11 Cubic Bridge
-- statement:
--   Definitions and structural lemmas for P11 Cubic Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/P11CubicBridge.lean

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_product_le_dual
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.KT19P11ReedSolomonCubicBridge
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
local instance p11Prime : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance p11NeZero : NeZero 11 := ⟨by norm_num⟩
noncomputable local instance p11PrimeQuditRegisterLabelFintype
    (Site : Type*) [Fintype Site] : Fintype (PrimeQuditRegisterLabel 11 Site) :=
  Fintype.ofFinite _
attribute [local instance] p11Prime p11NeZero p11PrimeQuditRegisterLabelFintype
def p11LogicalPolynomial : Fin 2 → Polynomial (ZMod 11)
  | 0 => Polynomial.X - 1
  | 1 => -Polynomial.X
def p11StabilizerPolynomial : Fin 2 → Polynomial (ZMod 11)
  | 0 => Polynomial.X * (Polynomial.X - 1)
  | 1 => Polynomial.X ^ 2 * (Polynomial.X - 1)
def p11RetainedEvaluation (polynomial : Polynomial (ZMod 11)) :
    Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  restrictKept 11 2 (evaluationMap 11 polynomial)
def p11LogicalRow : Fin 2 → Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  fun index => p11RetainedEvaluation (p11LogicalPolynomial index)
def p11StabilizerRow : Fin 2 → Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  fun index => p11RetainedEvaluation (p11StabilizerPolynomial index)
def p11Row : Fin 2 ⊕ Fin 2 → Word (ZMod 11) (KeptPunctureLocation 11 2) :=
  Sum.elim p11LogicalRow p11StabilizerRow
theorem p11Row_eq_retainedEvaluation (index : Fin 2 ⊕ Fin 2) :
    p11Row index = p11RetainedEvaluation
      (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial index) := by
  rcases index with index | index <;> rfl
def p11StabilizerCarrier : Submodule (ZMod 11) (Word (ZMod 11) (KeptPunctureLocation 11 2)) :=
  Submodule.span (ZMod 11) (Set.range p11StabilizerRow)
def p11RowCarrier : Submodule (ZMod 11) (Word (ZMod 11) (KeptPunctureLocation 11 2)) :=
  Submodule.span (ZMod 11) (Set.range p11Row)
theorem p11_logical_degreeLT (index : Fin 2) :
    p11LogicalPolynomial index ∈ Polynomial.degreeLT (ZMod 11) 4 := by
  fin_cases index
  · rw [p11LogicalPolynomial.eq_def, Polynomial.mem_degreeLT]
    calc
      (Polynomial.X - 1 : Polynomial (ZMod 11)).degree ≤
          max Polynomial.X.degree (1 : Polynomial (ZMod 11)).degree :=
        Polynomial.degree_sub_le _ _
      _ < (4 : WithBot ℕ) := by norm_num
  · rw [p11LogicalPolynomial.eq_def, Polynomial.mem_degreeLT]
    simpa using (show (Polynomial.X : Polynomial (ZMod 11)).degree < (4 : WithBot ℕ) by
      norm_num)
theorem p11_stabilizer_degreeLT (index : Fin 2) :
    p11StabilizerPolynomial index ∈ Polynomial.degreeLT (ZMod 11) 4 := by
  have hXdegree : (Polynomial.X : Polynomial (ZMod 11)).degree = (1 : WithBot ℕ) := by
    norm_num
  have hXsubDegree :
      ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree ≤ (1 : WithBot ℕ) := by
    calc
      _ ≤ max (Polynomial.X : Polynomial (ZMod 11)).degree
          (1 : Polynomial (ZMod 11)).degree := Polynomial.degree_sub_le _ _
      _ = (1 : WithBot ℕ) := by norm_num
  have hXXdegree :
      ((Polynomial.X : Polynomial (ZMod 11)) *
        (Polynomial.X : Polynomial (ZMod 11))).degree ≤ (1 : WithBot ℕ) + 1 := by
    calc
      _ ≤ (Polynomial.X : Polynomial (ZMod 11)).degree +
          (Polynomial.X : Polynomial (ZMod 11)).degree := Polynomial.degree_mul_le _ _
      _ = (1 : WithBot ℕ) + 1 := by rw [hXdegree]
  fin_cases index
  · rw [p11StabilizerPolynomial.eq_def, Polynomial.mem_degreeLT]
    calc
      (Polynomial.X * (Polynomial.X - 1) : Polynomial (ZMod 11)).degree ≤
          (Polynomial.X : Polynomial (ZMod 11)).degree +
            ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree :=
        Polynomial.degree_mul_le _ _
      _ = (1 : WithBot ℕ) + ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree := by
        rw [hXdegree]
      _ ≤ (1 : WithBot ℕ) + 1 :=
        add_le_add_right hXsubDegree (1 : WithBot ℕ)
      _ < (4 : WithBot ℕ) := by norm_num
  · rw [p11StabilizerPolynomial.eq_def, pow_two, Polynomial.mem_degreeLT]
    calc
      ((Polynomial.X * Polynomial.X) * (Polynomial.X - 1) : Polynomial (ZMod 11)).degree ≤
          ((Polynomial.X : Polynomial (ZMod 11)) *
              (Polynomial.X : Polynomial (ZMod 11))).degree +
            ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree :=
        Polynomial.degree_mul_le _ _
      _ ≤ ((1 : WithBot ℕ) + 1) +
          ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree :=
        add_le_add_left hXXdegree ((Polynomial.X : Polynomial (ZMod 11)) - 1).degree
      _ ≤ ((1 : WithBot ℕ) + 1) + 1 :=
        add_le_add_right hXsubDegree ((1 : WithBot ℕ) + 1)
      _ < (4 : WithBot ℕ) := by norm_num
theorem p11_row_degreeLT (index : Fin 2 ⊕ Fin 2) :
    (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial index) ∈
      Polynomial.degreeLT (ZMod 11) 4 := by
  rcases index with index | index
  · exact p11_logical_degreeLT index
  · exact p11_stabilizer_degreeLT index
theorem p11_selected_point_eq_zero_or_one
    (point : SelectedPunctureLocation 11 2) : point.1 = 0 ∨ point.1 = 1 := by
  have hlt : point.1.val < 2 := by
    simpa [selectedPunctureLocations] using (Finset.mem_filter.mp point.2).2
  interval_cases hvalue : point.1.val
  · left
    calc
      point.1 = (point.1.val : ZMod 11) := (ZMod.natCast_zmod_val point.1).symm
      _ = 0 := by simp [hvalue]
  · right
    calc
      point.1 = (point.1.val : ZMod 11) := (ZMod.natCast_zmod_val point.1).symm
      _ = 1 := by simp [hvalue]
noncomputable def p11SelectedPunctureEquivFin :
    SelectedPunctureLocation 11 2 ≃ Fin 2 := by
  refine
    { toFun := fun point => ⟨point.1.val, (Finset.mem_filter.mp point.2).2⟩
      invFun := fun index => ⟨(index.1 : ZMod 11), by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (index.2.trans_le (by norm_num : 2 ≤ 11))]
        exact index.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro point
    apply Subtype.ext
    exact ZMod.natCast_zmod_val point.1
  · intro index
    apply Fin.ext
    change ((index.1 : ZMod 11).val) = index.1
    exact ZMod.val_natCast_of_lt (index.2.trans_le (by norm_num : 2 ≤ 11))
theorem p11_stabilizer_restrictSelected_zero (index : Fin 2) :
    restrictSelected 11 2 (evaluationMap 11 (p11StabilizerPolynomial index)) = 0 := by
  ext point
  rcases p11_selected_point_eq_zero_or_one point with hpoint | hpoint
  · fin_cases index <;>
      simp [p11StabilizerPolynomial, evaluationMap, hpoint]
  · fin_cases index <;>
      simp [p11StabilizerPolynomial, evaluationMap, hpoint]
def p11CoefficientPolynomial (u h : Fin 2 → ZMod 11) : Polynomial (ZMod 11) :=
  (∑ index : Fin 2, u index • p11LogicalPolynomial index) +
    ∑ index : Fin 2, h index • p11StabilizerPolynomial index
theorem p11_coefficient_degreeLT (u h : Fin 2 → ZMod 11) :
    p11CoefficientPolynomial u h ∈ Polynomial.degreeLT (ZMod 11) 4 := by
  apply Submodule.add_mem
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod 11) 4) fun index _ =>
      Submodule.smul_mem _ _ (p11_logical_degreeLT index)
  · exact Submodule.sum_mem (Polynomial.degreeLT (ZMod 11) 4) fun index _ =>
      Submodule.smul_mem _ _ (p11_stabilizer_degreeLT index)
theorem p11_coefficient_restrictKept (u h : Fin 2 → ZMod 11) :
    p11RetainedEvaluation (p11CoefficientPolynomial u h) =
      (∑ index : Fin 2, u index • p11LogicalRow index) +
        ∑ index : Fin 2, h index • p11StabilizerRow index := by
  ext point
  simp [p11CoefficientPolynomial, p11RetainedEvaluation, evaluationMap,
    p11LogicalRow, p11StabilizerRow, Finset.sum_apply]
theorem p11_coefficient_eq_zero_of_restrictKept_zero
    (u h : Fin 2 → ZMod 11)
    (hzero : (∑ index : Fin 2, u index • p11LogicalRow index) +
        ∑ index : Fin 2, h index • p11StabilizerRow index = 0) :
    p11CoefficientPolynomial u h = 0 := by
  have hreduced : p11RetainedEvaluation (p11CoefficientPolynomial u h) = 0 := by
    rw [p11_coefficient_restrictKept]
    exact hzero
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (keptPunctureLocations 11 2)
  · exact (Polynomial.mem_degreeLT.mp (p11_coefficient_degreeLT u h)).trans_le (by
      norm_num [keptPunctureLocations_card])
  · exact WithBot.bot_lt_coe (keptPunctureLocations 11 2).card
  · intro point hpoint
    have hvalue := congrFun hreduced ⟨point, hpoint⟩
    simpa [p11RetainedEvaluation, evaluationMap] using hvalue
theorem p11_coefficients_zero_of_polynomial_zero (u h : Fin 2 → ZMod 11)
    (hzero : p11CoefficientPolynomial u h = 0) : u = 0 ∧ h = 0 := by
  have hconstant := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 0) hzero
  have hlinear := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 1) hzero
  have hquadratic := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 2) hzero
  have hcubic := congrArg (fun polynomial : Polynomial (ZMod 11) => polynomial.coeff 3) hzero
  norm_num [p11CoefficientPolynomial, p11LogicalPolynomial.eq_def,
    p11StabilizerPolynomial.eq_def, Fin.sum_univ_succ, Polynomial.coeff_add,
    Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_X,
    Polynomial.coeff_X_pow, Polynomial.coeff_one] at hconstant hlinear hquadratic hcubic
  ring_nf at hconstant hlinear hquadratic hcubic
  norm_num [Polynomial.coeff_add, Polynomial.coeff_neg, Polynomial.coeff_X_pow]
    at hconstant hlinear hquadratic hcubic
  have hu0 : u 0 = 0 := hconstant
  have hh1 : h 1 = 0 := hcubic
  have hh0 : h 0 = 0 := by
    simpa [hh1] using hquadratic
  have hu1 : u 1 = 0 := by
    simpa [hu0, hh0] using hlinear
  constructor
  · funext index
    fin_cases index
    · simpa using hu0
    · simpa using hu1
  · funext index
    fin_cases index
    · simpa using hh0
    · simpa using hh1
theorem p11_rows_independent (u h : Fin 2 → ZMod 11) :
    (∑ index : Fin 2, u index • p11LogicalRow index) +
      ∑ index : Fin 2, h index • p11StabilizerRow index = 0 → u = 0 ∧ h = 0 := by
  intro hzero
  exact p11_coefficients_zero_of_polynomial_zero u h
    (p11_coefficient_eq_zero_of_restrictKept_zero u h hzero)
theorem p11_full_cubic_zero (left middle right : Fin 2 ⊕ Fin 2) :
    cubicPairing 11
      (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
      (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
      (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right)) = 0 := by
  let leftBounded : Polynomial.degreeLT (ZMod 11) 4 :=
    ⟨Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left, p11_row_degreeLT left⟩
  let middleBounded : Polynomial.degreeLT (ZMod 11) 4 :=
    ⟨Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle, p11_row_degreeLT middle⟩
  let rightBounded : Polynomial.degreeLT (ZMod 11) 4 :=
    ⟨Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right, p11_row_degreeLT right⟩
  have hleft : evaluationLinearMap 11 4 leftBounded ∈ (reedSolomonCode 11 4).carrier :=
    evaluation_mem_reedSolomonCode 11 4 leftBounded
  have hmiddle : evaluationLinearMap 11 4 middleBounded ∈ (reedSolomonCode 11 4).carrier :=
    evaluation_mem_reedSolomonCode 11 4 middleBounded
  have hright : evaluationLinearMap 11 4 rightBounded ∈ (reedSolomonCode 11 4).carrier :=
    evaluation_mem_reedSolomonCode 11 4 rightBounded
  have hproduct : coordinatewiseProduct (evaluationLinearMap 11 4 leftBounded)
      (evaluationLinearMap 11 4 middleBounded) ∈ (reedSolomonCode 11 4).dual.carrier := by
    apply reedSolomonCode_product_le_dual 11 4 (by norm_num)
    rw [coordinatewiseProductCode]
    exact Submodule.subset_span ⟨evaluationLinearMap 11 4 leftBounded, hleft,
      evaluationLinearMap 11 4 middleBounded, hmiddle, rfl⟩
  have horthogonal := ((reedSolomonCode 11 4).mem_dual _).1 hproduct
    (evaluationLinearMap 11 4 rightBounded) hright
  simpa [leftBounded, middleBounded, rightBounded, cubicPairing, wordPairing_apply, dotProduct,
    coordinatewiseProduct, evaluationLinearMap_apply, evaluationMap] using horthogonal
theorem p11_retained_cubic_add_selected_cubic_eq_full
    (left middle right : Word (ZMod 11) (ZMod 11)) :
    cubicPairing 11 (restrictKept 11 2 left) (restrictKept 11 2 middle)
      (restrictKept 11 2 right) +
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) = cubicPairing 11 left middle right := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun point : ZMod 11 => point ∈ selectedPunctureLocations 11 2)
    (fun point => left point * middle point * right point)
  let complementKept :
      {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2} ≃
        KeptPunctureLocation 11 2 :=
    { toFun := fun point => ⟨point.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, point.2⟩⟩
      invFun := fun point => ⟨point.1, (Finset.mem_sdiff.mp point.2).2⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change (∑ point : KeptPunctureLocation 11 2,
      left point.1 * middle point.1 * right point.1) +
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) =
    ∑ point : ZMod 11, left point * middle point * right point
  have hequiv :
      (∑ point : {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) =
        ∑ point : KeptPunctureLocation 11 2, left point.1 * middle point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  calc
    (∑ point : KeptPunctureLocation 11 2, left point.1 * middle point.1 * right point.1) +
        (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
          left point.1 * middle point.1 * right point.1) =
        (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
          left point.1 * middle point.1 * right point.1) +
          (∑ point : KeptPunctureLocation 11 2,
            left point.1 * middle point.1 * right point.1) := by ac_rfl
    _ = (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
          left point.1 * middle point.1 * right point.1) +
          (∑ point : {point : ZMod 11 // ¬ point ∈ selectedPunctureLocations 11 2},
            left point.1 * middle point.1 * right point.1) := by rw [hequiv]
    _ = ∑ point : ZMod 11, left point * middle point * right point := hsplit
theorem p11_cubic_restrict_eq_full_of_selected_sum_zero
    (left middle right : Word (ZMod 11) (ZMod 11))
    (hselectedSum :
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        left point.1 * middle point.1 * right point.1) = 0) :
    cubicPairing 11 (restrictKept 11 2 left) (restrictKept 11 2 middle)
      (restrictKept 11 2 right) = cubicPairing 11 left middle right := by
  have hsplit := p11_retained_cubic_add_selected_cubic_eq_full left middle right
  rw [hselectedSum, add_zero] at hsplit
  exact hsplit
theorem p11_selected_cubic_sum_zero_of_restrictSelected_zero
    (left middle right : Word (ZMod 11) (ZMod 11))
    (hselected : restrictSelected 11 2 left = 0) :
    (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
      left point.1 * middle point.1 * right point.1) = 0 := by
  apply Finset.sum_eq_zero
  intro point _
  have hpoint : left point.1 = 0 := by
    simpa using congrFun hselected
      (⟨point.1, point.2⟩ : SelectedPunctureLocation 11 2)
  rw [hpoint]
  simp
theorem p11_stabilizer_triple_zero (left middle right : Fin 2 ⊕ Fin 2)
    (hcontains : (∃ index, left = Sum.inr index) ∨ (∃ index, middle = Sum.inr index) ∨
      (∃ index, right = Sum.inr index)) :
    cubicPairing 11 (p11Row left) (p11Row middle) (p11Row right) = 0 := by
  rcases hcontains with ⟨index, rfl⟩ | ⟨index, rfl⟩ | ⟨index, rfl⟩
  · rw [p11Row_eq_retainedEvaluation (Sum.inr index),
      p11Row_eq_retainedEvaluation middle,
      p11Row_eq_retainedEvaluation right]
    simp only [p11RetainedEvaluation, Sum.elim_inr]
    calc
      _ = cubicPairing 11 (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right)) :=
        p11_cubic_restrict_eq_full_of_selected_sum_zero
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right))
          (p11_selected_cubic_sum_zero_of_restrictSelected_zero _ _ _
            (p11_stabilizer_restrictSelected_zero index))
      _ = 0 := p11_full_cubic_zero (Sum.inr index) middle right
  · rw [p11Row_eq_retainedEvaluation left,
      p11Row_eq_retainedEvaluation (Sum.inr index),
      p11Row_eq_retainedEvaluation right]
    simp only [p11RetainedEvaluation, Sum.elim_inr]
    calc
      _ = cubicPairing 11
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right)) :=
        p11_cubic_restrict_eq_full_of_selected_sum_zero
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (p11_selected_cubic_sum_zero_of_restrictSelected_zero
                (evaluationMap 11 (p11StabilizerPolynomial index))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial right))
                (p11_stabilizer_restrictSelected_zero index)))
      _ = 0 := p11_full_cubic_zero left (Sum.inr index) right
  · rw [p11Row_eq_retainedEvaluation left,
      p11Row_eq_retainedEvaluation middle,
      p11Row_eq_retainedEvaluation (Sum.inr index)]
    simp only [p11RetainedEvaluation, Sum.elim_inr]
    calc
      _ = cubicPairing 11
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (p11StabilizerPolynomial index)) :=
        p11_cubic_restrict_eq_full_of_selected_sum_zero
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
          (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
          (evaluationMap 11 (p11StabilizerPolynomial index))
          (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (p11_selected_cubic_sum_zero_of_restrictSelected_zero
                (evaluationMap 11 (p11StabilizerPolynomial index))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial left))
                (evaluationMap 11 (Sum.elim p11LogicalPolynomial p11StabilizerPolynomial middle))
                (p11_stabilizer_restrictSelected_zero index)))
      _ = 0 := p11_full_cubic_zero left middle (Sum.inr index)
theorem p11_logical_offDiagonal_zero (left middle right : Fin 2)
    (hnot : ¬ (left = middle ∧ middle = right)) :
    cubicPairing 11 (p11LogicalRow left) (p11LogicalRow middle) (p11LogicalRow right) = 0 := by
  have hselected :
      (∑ point : {point : ZMod 11 // point ∈ selectedPunctureLocations 11 2},
        evaluationMap 11 (p11LogicalPolynomial left) point.1 *
          evaluationMap 11 (p11LogicalPolynomial middle) point.1 *
            evaluationMap 11 (p11LogicalPolynomial right) point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    rcases p11_selected_point_eq_zero_or_one
      (⟨point.1, point.2⟩ : SelectedPunctureLocation 11 2) with hpoint | hpoint
    · rw [hpoint]
      fin_cases left <;> fin_cases middle <;> fin_cases right <;>
        simp_all [p11LogicalPolynomial, evaluationMap]
    · rw [hpoint]
      fin_cases left <;> fin_cases middle <;> fin_cases right <;>
        simp_all [p11LogicalPolynomial, evaluationMap]
  have htransport := p11_cubic_restrict_eq_full_of_selected_sum_zero
    (evaluationMap 11 (p11LogicalPolynomial left))
    (evaluationMap 11 (p11LogicalPolynomial middle))
    (evaluationMap 11 (p11LogicalPolynomial right)) hselected
  simpa [p11LogicalRow, p11RetainedEvaluation] using htransport.trans
    (p11_full_cubic_zero (Sum.inl left) (Sum.inl middle) (Sum.inl right))
noncomputable def p11CubicRowFamily :
    CubicRowFamily 11 (Fin 2) (Fin 2) (KeptPunctureLocation 11 2) where
  logicalRow := p11LogicalRow
  stabilizerRow := p11StabilizerRow
  rowIndependent := p11_rows_independent
  stabilizerTriple_zero := p11_stabilizer_triple_zero
  logicalTriple_offDiagonal_zero := p11_logical_offDiagonal_zero
end QEC.Distillation.KT19P11ReedSolomonCubicBridge


