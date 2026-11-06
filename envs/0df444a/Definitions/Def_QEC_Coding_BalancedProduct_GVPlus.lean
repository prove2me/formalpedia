-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
-- name    : QEC_Coding_BalancedProduct_GVPlus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:40:53.685499+00:00
-- url     : https://prove2.me/theorems/47fe3c61-e8d6-4366-b2d3-ac8dc509e6e6
-- title:
--   GVPlus
-- statement:
--   Definitions and structural lemmas for GVPlus, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/GVPlus.lean

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.FieldTheory.Finiteness
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace BalancedProduct
namespace GVPlus
open Classical
def systematicEncode {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2))
    (m : Fin k → ZMod 2) : Sum (Fin k) (Fin r) → ZMod 2
  | Sum.inl i => m i
  | Sum.inr j => Matrix.vecMul m A j
def systematicEncodeLinear {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Sum (Fin k) (Fin r) → ZMod 2) where
  toFun := systematicEncode A
  map_add' := by
    intro x y
    funext q
    cases q with
    | inl i => rfl
    | inr j =>
        simp [systematicEncode, Matrix.vecMul, dotProduct, Finset.sum_add_distrib,
          add_mul]
  map_smul' := by
    intro a x
    funext q
    cases q with
    | inl i => rfl
    | inr j =>
        simp [systematicEncode, Matrix.vecMul, dotProduct, Finset.mul_sum,
          mul_assoc]
@[simp]
theorem systematicEncodeLinear_apply {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) (m : Fin k → ZMod 2) :
    systematicEncodeLinear A m = systematicEncode A m :=
  rfl
def systematicCode {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) :
    LinearCode (ZMod 2) (Sum (Fin k) (Fin r)) where
  carrier := LinearMap.range (systematicEncodeLinear A)
@[simp]
theorem mem_systematicCode {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2))
    (x : Sum (Fin k) (Fin r) → ZMod 2) :
    x ∈ (systematicCode A).carrier ↔
      ∃ m : Fin k → ZMod 2, systematicEncode A m = x := by
  simp [systematicCode, systematicEncodeLinear]
def systematicDualEncode {k r : Nat}
    (A : Matrix (Fin k) (Fin r) (ZMod 2))
    (y : Fin r → ZMod 2) : Sum (Fin k) (Fin r) → ZMod 2
  | Sum.inl i => -(Matrix.mulVec A y i)
  | Sum.inr j => y j
theorem binary_eq_one_of_ne_zero (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
  apply ZMod.val_injective 2
  rw [ZMod.val_one]
  have hxval : x.val ≠ 0 := (ZMod.val_eq_zero x).not.mpr hx
  have hxlt : x.val < 2 := x.val_lt
  omega
def supportWord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) : Word (ZMod 2) ι :=
  fun i => if i ∈ S then 1 else 0
@[simp]
theorem hammingSupport_supportWord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) :
    hammingSupport (supportWord S) = S := by
  ext i
  simp [hammingSupport, supportWord]
@[simp]
theorem supportWord_hammingSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Word (ZMod 2) ι) :
    supportWord (hammingSupport x) = x := by
  funext i
  by_cases hi : x i = 0
  · simp [supportWord, hammingSupport, hi]
  · rw [binary_eq_one_of_ne_zero (x i) hi]
    simp only [supportWord, hammingSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, if_pos hi]
abbrev LowWordOn (ι : Type*) [Fintype ι] (d : Nat) :=
  {x : Word (ZMod 2) ι // HammingWeight x < d}
abbrev LowWord (n d : Nat) := LowWordOn (Fin n) d
abbrev LowSupportOn (ι : Type*) (d : Nat) :=
  Σ i : Fin d, Set.powersetCard ι i.1
def lowWordEquivLowSupportOn
    (ι : Type*) [Fintype ι] [DecidableEq ι] (d : Nat) :
    LowWordOn ι d ≃ LowSupportOn ι d where
  toFun x :=
    ⟨⟨HammingWeight x.1, x.2⟩,
      ⟨hammingSupport x.1, HammingWeight_eq_card_hammingSupport x.1⟩⟩
  invFun s :=
    ⟨supportWord s.2.1, by
      simp [HammingWeight_eq_card_hammingSupport, s.1.2]⟩
  left_inv x := by
    apply Subtype.ext
    exact supportWord_hammingSupport x.1
  right_inv s := by
    apply Sigma.subtype_ext
    · simp [HammingWeight_eq_card_hammingSupport]
    · exact hammingSupport_supportWord s.2.1
theorem card_lowWordOn
    (ι : Type*) [Fintype ι] [DecidableEq ι] (d : Nat) :
    Fintype.card (LowWordOn ι d) =
      ∑ i ∈ Finset.range d, Nat.choose (Fintype.card ι) i := by
  rw [Fintype.card_congr (lowWordEquivLowSupportOn ι d), Fintype.card_sigma]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card,
    Nat.card_eq_fintype_card]
def linearFiberEquivKer
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) (x₀ : V) :
    {x : V // f x = f x₀} ≃ f.ker where
  toFun x := ⟨x.1 - x₀, by simp [x.2]⟩
  invFun z := ⟨z.1 + x₀, by simp⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp
theorem card_linearMap_fiber_of_surjective
    {F V W : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Fintype W]
    (f : V →ₗ[F] W) (hf : Function.Surjective f) (y : W) :
    Fintype.card {x : V // f x = y} =
      Fintype.card F ^ (Module.finrank F V - Module.finrank F W) := by
  obtain ⟨x₀, hx₀⟩ := hf y
  subst y
  rw [Fintype.card_congr (linearFiberEquivKer f x₀),
    @Module.card_eq_pow_finrank F f.ker _ _ _ _ _]
  congr 1
  have hrange : Module.finrank F f.range = Module.finrank F W := by
    rw [LinearMap.range_eq_top.mpr hf, finrank_top]
  have hrankNullity := f.finrank_range_add_finrank_ker
  omega
theorem natCard_linearMap_fiber_of_surjective
    {F V W : Type*} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Finite V]
    [AddCommGroup W] [Module F W] [Finite W]
    (f : V →ₗ[F] W) (hf : Function.Surjective f) (y : W) :
    Nat.card {x : V // f x = y} =
      Nat.card F ^ (Module.finrank F V - Module.finrank F W) := by
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite W
  simpa only [Nat.card_eq_fintype_card] using
    card_linearMap_fiber_of_surjective f hf y
def rowEvaluation {k r : Nat} (m : Fin k → ZMod 2) :
    Matrix (Fin k) (Fin r) (ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) where
  toFun A := Matrix.vecMul m A
  map_add' := by
    intro A B
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro a A
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_left_comm]
@[simp]
theorem rowEvaluation_apply {k r : Nat} (m : Fin k → ZMod 2)
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) :
    rowEvaluation m A = Matrix.vecMul m A :=
  rfl
theorem rowEvaluation_surjective {k r : Nat} {m : Fin k → ZMod 2}
    (hm : m ≠ 0) : Function.Surjective (rowEvaluation (r := r) m) := by
  have hexists : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  obtain ⟨i, hi⟩ := hexists
  have hmi : m i = 1 := binary_eq_one_of_ne_zero (m i) hi
  intro y
  let A : Matrix (Fin k) (Fin r) (ZMod 2) :=
    fun i' j => if i' = i then y j else 0
  refine ⟨A, ?_⟩
  funext j
  change Matrix.vecMul m A j = y j
  rw [Matrix.vecMul, dotProduct, Fintype.sum_eq_single i]
  · simp [A, hmi]
  · intro i' hi'
    simp [A, hi']
def columnEvaluation {k r : Nat} (y : Fin r → ZMod 2) :
    Matrix (Fin k) (Fin r) (ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun A := Matrix.mulVec A y
  map_add' := by
    intro A B
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro a A
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
@[simp]
theorem columnEvaluation_apply {k r : Nat} (y : Fin r → ZMod 2)
    (A : Matrix (Fin k) (Fin r) (ZMod 2)) :
    columnEvaluation y A = Matrix.mulVec A y :=
  rfl
theorem columnEvaluation_surjective {k r : Nat} {y : Fin r → ZMod 2}
    (hy : y ≠ 0) : Function.Surjective (columnEvaluation (k := k) y) := by
  have hexists : ∃ j, y j ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  obtain ⟨j, hj⟩ := hexists
  have hyj : y j = 1 := binary_eq_one_of_ne_zero (y j) hj
  intro x
  let A : Matrix (Fin k) (Fin r) (ZMod 2) :=
    fun i j' => if j' = j then x i else 0
  refine ⟨A, ?_⟩
  funext i
  change Matrix.mulVec A y i = x i
  rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_single j]
  · simp [A, hyj]
  · intro j' hj'
    simp [A, hj']
theorem card_le_card_mul_of_fiber_le
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : α → β) (N : Nat)
    (hfiber : ∀ b : β, Fintype.card {a : α // f a = b} ≤ N) :
    Fintype.card α ≤ Fintype.card β * N := by
  classical
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := f) (by simp)]
  calc
    (∑ b ∈ (Finset.univ : Finset β),
        ((Finset.univ : Finset α).filter fun a => f a = b).card) ≤
        ∑ _b ∈ (Finset.univ : Finset β), N := by
      apply Finset.sum_le_sum
      intro b _hb
      simpa only [Fintype.card_subtype] using hfiber b
    _ = Fintype.card β * N := by simp
abbrev LocalMatrix := Matrix (Fin 202) (Fin 200) (ZMod 2)
local instance localMatrixFintype : Fintype LocalMatrix :=
  Fintype.ofFinite LocalMatrix
abbrev LocalCoordinate := Sum (Fin 202) (Fin 200)
@[simp]
theorem localCoordinate_card : Fintype.card LocalCoordinate = 402 := by
  decide +kernel
def leftPart (w : Word (ZMod 2) LocalCoordinate) : Fin 202 → ZMod 2 :=
  fun i => w (Sum.inl i)
def rightPart (w : Word (ZMod 2) LocalCoordinate) : Fin 200 → ZMod 2 :=
  fun j => w (Sum.inr j)
abbrev PrimalWitness :=
  {p : (Fin 202 → ZMod 2) × LocalMatrix //
    p.1 ≠ 0 ∧ HammingWeight (systematicEncode p.2 p.1) < 41}
abbrev DualWitness :=
  {p : (Fin 200 → ZMod 2) × LocalMatrix //
    p.1 ≠ 0 ∧ HammingWeight (systematicDualEncode p.2 p.1) < 41}
def primalWitnessWord (z : PrimalWitness) : LowWordOn LocalCoordinate 41 :=
  ⟨systematicEncode z.1.2 z.1.1, z.2.2⟩
def dualWitnessWord (z : DualWitness) : LowWordOn LocalCoordinate 41 :=
  ⟨systematicDualEncode z.1.2 z.1.1, z.2.2⟩
def primalFiberCard : Nat :=
  Fintype.card (ZMod 2) ^
    (Module.finrank (ZMod 2) LocalMatrix -
      Module.finrank (ZMod 2) (Fin 200 → ZMod 2))
def dualFiberCard : Nat :=
  Fintype.card (ZMod 2) ^
    (Module.finrank (ZMod 2) LocalMatrix -
      Module.finrank (ZMod 2) (Fin 202 → ZMod 2))
theorem card_primalWitnessWord_fiber_le
    (w : LowWordOn LocalCoordinate 41) :
    Fintype.card {z : PrimalWitness // primalWitnessWord z = w} ≤
      primalFiberCard := by
  classical
  let fiber := {z : PrimalWitness // primalWitnessWord z = w}
  by_cases hnonempty : Nonempty fiber
  · let z₀ : fiber := Classical.choice hnonempty
    have hzword : systematicEncode z₀.1.1.2 z₀.1.1.1 = w.1 :=
      congrArg Subtype.val z₀.2
    have hleft : z₀.1.1.1 = leftPart w.1 := by
      funext i
      exact congrFun hzword (Sum.inl i)
    have hleft0 : leftPart w.1 ≠ 0 := by
      rw [← hleft]
      exact z₀.1.2.1
    let target := {A : LocalMatrix //
      rowEvaluation (leftPart w.1) A = rightPart w.1}
    let encodeFiber : fiber → target := fun z =>
      ⟨z.1.1.2, by
        funext j
        have hz : systematicEncode z.1.1.2 z.1.1.1 = w.1 :=
          congrArg Subtype.val z.2
        have hm (i : Fin 202) : z.1.1.1 i = leftPart w.1 i :=
          congrFun hz (Sum.inl i)
        change Matrix.vecMul (leftPart w.1) z.1.1.2 j = w.1 (Sum.inr j)
        rw [← congrFun hz (Sum.inr j)]
        congr 1
        exact funext fun i => (hm i).symm⟩
    have hinjective : Function.Injective encodeFiber := by
      intro z z' hzz'
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · funext i
        have hz := congrArg Subtype.val z.2
        have hz' := congrArg Subtype.val z'.2
        exact (congrFun hz (Sum.inl i)).trans
          (congrFun hz' (Sum.inl i)).symm
      · exact congrArg Subtype.val hzz'
    calc
      Fintype.card fiber ≤ Fintype.card target :=
        Fintype.card_le_of_injective encodeFiber hinjective
      _ = primalFiberCard := by
        unfold target primalFiberCard
        rw [← Nat.card_eq_fintype_card]
        simpa only [rowEvaluation_apply, Nat.card_eq_fintype_card] using
            natCard_linearMap_fiber_of_surjective
            (rowEvaluation (leftPart w.1))
            (rowEvaluation_surjective hleft0) (rightPart w.1)
  · have hempty : IsEmpty fiber := not_nonempty_iff.mp hnonempty
    simp [Fintype.card_eq_zero]
theorem card_dualWitnessWord_fiber_le
    (w : LowWordOn LocalCoordinate 41) :
    Fintype.card {z : DualWitness // dualWitnessWord z = w} ≤
      dualFiberCard := by
  classical
  let fiber := {z : DualWitness // dualWitnessWord z = w}
  by_cases hnonempty : Nonempty fiber
  · let z₀ : fiber := Classical.choice hnonempty
    have hzword : systematicDualEncode z₀.1.1.2 z₀.1.1.1 = w.1 :=
      congrArg Subtype.val z₀.2
    have hright : z₀.1.1.1 = rightPart w.1 := by
      funext j
      exact congrFun hzword (Sum.inr j)
    have hright0 : rightPart w.1 ≠ 0 := by
      rw [← hright]
      exact z₀.1.2.1
    let target := {A : LocalMatrix //
      columnEvaluation (rightPart w.1) A = fun i => -leftPart w.1 i}
    let encodeFiber : fiber → target := fun z =>
      ⟨z.1.1.2, by
        funext i
        have hz : systematicDualEncode z.1.1.2 z.1.1.1 = w.1 :=
          congrArg Subtype.val z.2
        have hy (j : Fin 200) : z.1.1.1 j = rightPart w.1 j :=
          congrFun hz (Sum.inr j)
        change Matrix.mulVec z.1.1.2 (rightPart w.1) i = -w.1 (Sum.inl i)
        rw [← congrFun hz (Sum.inl i)]
        simp only [systematicDualEncode, neg_neg]
        congr 1
        exact funext fun j => (hy j).symm⟩
    have hinjective : Function.Injective encodeFiber := by
      intro z z' hzz'
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · funext j
        have hz := congrArg Subtype.val z.2
        have hz' := congrArg Subtype.val z'.2
        exact (congrFun hz (Sum.inr j)).trans
          (congrFun hz' (Sum.inr j)).symm
      · exact congrArg Subtype.val hzz'
    calc
      Fintype.card fiber ≤ Fintype.card target :=
        Fintype.card_le_of_injective encodeFiber hinjective
      _ = dualFiberCard := by
        unfold target dualFiberCard
        rw [← Nat.card_eq_fintype_card]
        simpa only [columnEvaluation_apply, Nat.card_eq_fintype_card] using
            natCard_linearMap_fiber_of_surjective
            (columnEvaluation (rightPart w.1))
            (columnEvaluation_surjective hright0) (fun i => -leftPart w.1 i)
  · have hempty : IsEmpty fiber := not_nonempty_iff.mp hnonempty
    simp [Fintype.card_eq_zero]
theorem card_primalWitness_le :
    Fintype.card PrimalWitness ≤
      Fintype.card (LowWordOn LocalCoordinate 41) * primalFiberCard :=
  card_le_card_mul_of_fiber_le primalWitnessWord primalFiberCard
    card_primalWitnessWord_fiber_le
theorem card_dualWitness_le :
    Fintype.card DualWitness ≤
      Fintype.card (LowWordOn LocalCoordinate 41) * dualFiberCard :=
  card_le_card_mul_of_fiber_le dualWitnessWord dualFiberCard
    card_dualWitnessWord_fiber_le
theorem card_localLowWord_lt :
    Fintype.card (LowWordOn LocalCoordinate 41) < 2 ^ 185 := by
  rw [card_lowWordOn, localCoordinate_card]
  decide +kernel
theorem primalFiberCard_eq : primalFiberCard = 2 ^ (201 * 200) := by
  unfold primalFiberCard
  have hbase : Fintype.card (ZMod 2) = 2 := by decide +kernel
  rw [hbase]
  congr 1
  norm_num [LocalMatrix, Module.finrank_matrix,
    Module.finrank_fintype_fun_eq_card]
theorem dualFiberCard_eq : dualFiberCard = 2 ^ (202 * 199) := by
  unfold dualFiberCard
  have hbase : Fintype.card (ZMod 2) = 2 := by decide +kernel
  rw [hbase]
  congr 1
  norm_num [LocalMatrix, Module.finrank_matrix,
    Module.finrank_fintype_fun_eq_card]
theorem localMatrix_card : Fintype.card LocalMatrix = 2 ^ (202 * 200) := by
  rw [@Module.card_eq_pow_finrank (ZMod 2) LocalMatrix _ _ _ _ _]
  have hbase : Fintype.card (ZMod 2) = 2 := by decide +kernel
  rw [hbase]
  congr 1
  norm_num [LocalMatrix, Module.finrank_matrix]
def PrimalBad (A : LocalMatrix) : Prop :=
  ∃ m : Fin 202 → ZMod 2,
    m ≠ 0 ∧ HammingWeight (systematicEncode A m) < 41
def DualBad (A : LocalMatrix) : Prop :=
  ∃ y : Fin 200 → ZMod 2,
    y ≠ 0 ∧ HammingWeight (systematicDualEncode A y) < 41
def Bad (A : LocalMatrix) : Prop := PrimalBad A ∨ DualBad A
abbrev PrimalBadMatrix := {A : LocalMatrix // PrimalBad A}
abbrev DualBadMatrix := {A : LocalMatrix // DualBad A}
abbrev BadMatrix := {A : LocalMatrix // Bad A}
noncomputable def primalBadToWitness (A : PrimalBadMatrix) : PrimalWitness :=
  ⟨⟨Classical.choose A.2, A.1⟩, Classical.choose_spec A.2⟩
theorem primalBadToWitness_injective : Function.Injective primalBadToWitness := by
  intro A B hAB
  apply Subtype.ext
  exact congrArg (fun z : PrimalWitness => z.1.2) hAB
noncomputable def dualBadToWitness (A : DualBadMatrix) : DualWitness :=
  ⟨⟨Classical.choose A.2, A.1⟩, Classical.choose_spec A.2⟩
theorem dualBadToWitness_injective : Function.Injective dualBadToWitness := by
  intro A B hAB
  apply Subtype.ext
  exact congrArg (fun z : DualWitness => z.1.2) hAB
theorem card_primalBadMatrix_le :
    Fintype.card PrimalBadMatrix ≤ Fintype.card PrimalWitness :=
  Fintype.card_le_of_injective primalBadToWitness primalBadToWitness_injective
theorem card_dualBadMatrix_le :
    Fintype.card DualBadMatrix ≤ Fintype.card DualWitness :=
  Fintype.card_le_of_injective dualBadToWitness dualBadToWitness_injective
noncomputable def badToSum (A : BadMatrix) :
    Sum PrimalBadMatrix DualBadMatrix := by
  by_cases hA : PrimalBad A.1
  · exact Sum.inl ⟨A.1, hA⟩
  · exact Sum.inr ⟨A.1, A.2.resolve_left hA⟩
@[simp]
theorem badToSum_value (A : BadMatrix) :
    (match badToSum A with
      | Sum.inl a => a.1
      | Sum.inr a => a.1) = A.1 := by
  by_cases hA : PrimalBad A.1 <;> simp [badToSum, hA]
theorem badToSum_injective : Function.Injective badToSum := by
  intro A B hAB
  apply Subtype.ext
  have hval := congrArg
    (fun z : Sum PrimalBadMatrix DualBadMatrix =>
      match z with
      | Sum.inl a => a.1
      | Sum.inr a => a.1) hAB
  simpa only [badToSum_value] using hval
theorem card_badMatrix_le :
    Fintype.card BadMatrix ≤
      Fintype.card (LowWordOn LocalCoordinate 41) * primalFiberCard +
      Fintype.card (LowWordOn LocalCoordinate 41) * dualFiberCard := by
  calc
    Fintype.card BadMatrix ≤
        Fintype.card (Sum PrimalBadMatrix DualBadMatrix) :=
      Fintype.card_le_of_injective badToSum badToSum_injective
    _ = Fintype.card PrimalBadMatrix + Fintype.card DualBadMatrix := by simp
    _ ≤ Fintype.card PrimalWitness + Fintype.card DualWitness :=
      Nat.add_le_add card_primalBadMatrix_le card_dualBadMatrix_le
    _ ≤ _ := Nat.add_le_add card_primalWitness_le card_dualWitness_le
theorem numerical_bad_bound :
    Fintype.card (LowWordOn LocalCoordinate 41) * 2 ^ (201 * 200) +
        Fintype.card (LowWordOn LocalCoordinate 41) * 2 ^ (202 * 199) <
      2 ^ (202 * 200) := by
  have hball := card_localLowWord_lt
  have hp : 0 < 2 ^ (201 * 200) := pow_pos (by norm_num) _
  have hd : 0 < 2 ^ (202 * 199) := pow_pos (by norm_num) _
  calc
    _ < 2 ^ 185 * 2 ^ (201 * 200) +
        2 ^ 185 * 2 ^ (202 * 199) :=
      Nat.add_lt_add
        (Nat.mul_lt_mul_of_pos_right hball hp)
        (Nat.mul_lt_mul_of_pos_right hball hd)
    _ = 2 ^ 40385 + 2 ^ 40383 := by
      rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ 40399 + 2 ^ 40399 := by
      apply Nat.add_le_add <;>
        apply pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : Nat)) <;> omega
    _ = 2 ^ 40400 := by
      calc
        2 ^ 40399 + 2 ^ 40399 = 2 ^ 1 * 2 ^ 40399 := by
          rw [pow_one, two_mul]
        _ = 2 ^ (1 + 40399) := (pow_add 2 1 40399).symm
        _ = 2 ^ 40400 := by norm_num
    _ = 2 ^ (202 * 200) := by norm_num
theorem card_badMatrix_lt :
    Fintype.card BadMatrix < Fintype.card LocalMatrix := by
  rw [localMatrix_card]
  exact card_badMatrix_le.trans_lt (by
    rw [primalFiberCard_eq, dualFiberCard_eq]
    exact numerical_bad_bound)
theorem exists_goodMatrix : ∃ A : LocalMatrix, ¬Bad A := by
  by_contra h
  push Not at h
  let e : LocalMatrix ≃ BadMatrix :=
    { toFun := fun A : LocalMatrix => (⟨A, h A⟩ : BadMatrix)
      invFun := fun A : BadMatrix => A.1
      left_inv := fun _ => rfl
      right_inv := fun A => Subtype.ext rfl }
  have heq := Fintype.card_congr e
  exact (Nat.ne_of_lt card_badMatrix_lt) heq.symm
noncomputable def localMatrix : LocalMatrix := Classical.choose exists_goodMatrix
noncomputable def localCode : LinearCode (ZMod 2) LocalCoordinate :=
  systematicCode localMatrix
end GVPlus
end BalancedProduct
end Coding
end QEC


