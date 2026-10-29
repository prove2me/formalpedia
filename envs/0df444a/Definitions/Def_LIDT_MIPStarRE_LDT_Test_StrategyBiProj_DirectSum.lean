-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
-- name    : LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:39:53.544845+00:00
-- url     : https://prove2.me/theorems/f0a54b5b-0725-434a-9dfa-06411f3a5bdc
-- title:
--   LIDT definitions: LDT / Test / StrategyBiProj / DirectSum
-- statement:
--   This bundle defines the direct-sum carriers and block embeddings used to symmetrize heterogeneous two-space strategies. It re-associates role registers, places operators in the two occupied role sectors, swaps density operators, and records the normalizing scale.
--
--   Principal definitions:
--   - `LocalCarrierSum`: the direct-sum local carrier for the two original spaces.
--   - `RoleRegisterLocal`: the role-bit plus direct-sum carrier used by the heterogeneous symmetrization.
--   - `roleRegisterPairLocalEquiv`: reassociation between pairs of role-register carriers and the original tensor layout.
--   - `localPairABBlock`: embedding of an Alice-Bob operator into the corresponding direct-sum block.
--   - `localPairBABlock`: embedding of a Bob-Alice operator into the reversed direct-sum block.
--   - `heterogeneousSwapDensity`: density-operator swap from `ιA x ιB` to `ιB x ιA`.
--   - `rolePairDirectSumCond`: placement of a direct-sum bipartite operator in a selected role-sector pair.
--   - `roleRegisterDensityScale`: the scalar normalization used for the direct-sum role-register state.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyBiProj/DirectSum.lean#L24-L737

-- Generated from MIPStarRE/LDT/Test/StrategyBiProj/DirectSum.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

/-!
# Two-Space Projective Strategies: Direct-Sum State Blocks

This module contains the role-register direct-sum carriers and block-state
construction used to symmetrize a heterogeneous projective strategy.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

/-! ### Direct-sum role-register helpers -/

/-- Direct-sum carrier for the future heterogeneous role symmetrization.

For a two-space strategy with Alice carrier `ιA` and Bob carrier `ιB`, the later
symmetrized local space will use this tagged direct sum so that Alice's operators
occupy the `Sum.inl` block and Bob's operators occupy the `Sum.inr` block. -/
abbrev LocalCarrierSum (ιA ιB : Type*) := Sum ιA ιB

/-- Local carrier planned for the heterogeneous symmetrization bridge: a role bit
and a direct-sum carrier. This is the direct-sum analogue of the current
same-space target `Role × ι` in `StrategyRole.lean`. -/
abbrev RoleRegisterLocal (ιA ιB : Type*) := Role × LocalCarrierSum ιA ιB

/-- Reassociate role bits and direct-sum carriers.

This is the public heterogeneous analogue of the same-space role-register
reassociation used internally by `StrategyRole.lean`. It prepares the target
shape for reindexing block states on
`(Role × (ιA ⊕ ιB)) × (Role × (ιA ⊕ ιB))`. -/
def roleRegisterPairLocalEquiv (ιA ιB : Type*) :
    ((Role × Role) × (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) ≃
      (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-! ### Direct-sum block states for heterogeneous role symmetrization -/

/-- Embed an operator on Alice's and Bob's original tensor product into the
`(Sum.inl _) × (Sum.inr _)` block of the direct-sum tensor product. -/
noncomputable def localPairABBlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB) :=
  Matrix.of fun x y =>
    match x, y with
    | (Sum.inl i, Sum.inr j), (Sum.inl i', Sum.inr j') => X (i, j) (i', j')
    | _, _ => 0

/-- Embed an operator on Bob's and Alice's original tensor product into the
`(Sum.inr _) × (Sum.inl _)` block of the direct-sum tensor product. -/
noncomputable def localPairBABlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB) :=
  Matrix.of fun x y =>
    match x, y with
    | (Sum.inr i, Sum.inl j), (Sum.inr i', Sum.inl j') => X (i, j) (i', j')
    | _, _ => 0

@[simp] theorem localPairABBlock_AB_AB {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) (i i' : ιA) (j j' : ιB) :
    localPairABBlock X (Sum.inl i, Sum.inr j) (Sum.inl i', Sum.inr j') =
      X (i, j) (i', j') :=
  rfl

@[simp] theorem localPairBABlock_BA_BA {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) (i i' : ιB) (j j' : ιA) :
    localPairBABlock X (Sum.inr i, Sum.inl j) (Sum.inr i', Sum.inl j') =
      X (i, j) (i', j') :=
  rfl

@[simp] theorem localPairABBlock_conjTranspose {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    (localPairABBlock X)ᴴ = localPairABBlock Xᴴ := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [localPairABBlock]

@[simp] theorem localPairBABlock_conjTranspose {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    (localPairBABlock X)ᴴ = localPairBABlock Xᴴ := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [localPairBABlock]

@[simp] theorem localPairABBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιA × ιB)) :
    localPairABBlock X * localPairABBlock Y = localPairABBlock (X * Y) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ with
      | inl j =>
          cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ with
          | inl i' =>
              cases y₂ with
              | inl j' => simp [localPairABBlock, Matrix.mul_apply]
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairABBlock, Matrix.of_apply,
                    zero_mul, Finset.sum_const_zero, zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιA => fun y : ιB =>
                      X (i, j) (x, y) * Y (x, y) (i', j'))).symm
          | inr i' =>
              cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]

@[simp] theorem localPairBABlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιB × ιA)) :
    localPairBABlock X * localPairBABlock Y = localPairBABlock (X * Y) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ with
      | inl j =>
          cases y₁ with
          | inl i' =>
              cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]
          | inr i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairBABlock, Matrix.of_apply,
                    zero_mul, Finset.sum_const_zero, zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιB => fun y : ιA =>
                      X (i, j) (x, y) * Y (x, y) (i', j'))).symm
              | inr j' => simp [localPairBABlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]

theorem localPairABBlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {X : MIPStarRE.Quantum.Op (ιA × ιB)} (hX : 0 ≤ X) :
    0 ≤ localPairABBlock X := by
  classical
  let := Fintype.ofFinite ιA
  let := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hX ⊢
  rcases hX with ⟨C, hC⟩
  refine ⟨localPairABBlock C, ?_⟩
  change localPairABBlock X = (localPairABBlock C)ᴴ * localPairABBlock C
  rw [localPairABBlock_conjTranspose, localPairABBlock_mul]
  exact congrArg localPairABBlock hC

theorem localPairBABlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {X : MIPStarRE.Quantum.Op (ιB × ιA)} (hX : 0 ≤ X) :
    0 ≤ localPairBABlock X := by
  classical
  let := Fintype.ofFinite ιA
  let := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hX ⊢
  rcases hX with ⟨C, hC⟩
  refine ⟨localPairBABlock C, ?_⟩
  change localPairBABlock X = (localPairBABlock C)ᴴ * localPairBABlock C
  rw [localPairBABlock_conjTranspose, localPairBABlock_mul]
  exact congrArg localPairBABlock hC

/-- Swap an operator on `ιA × ιB` to one on `ιB × ιA`. -/
noncomputable def heterogeneousSwapDensity {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.Op (ιB × ιA) :=
  Matrix.reindex (Equiv.prodComm ιA ιB) (Equiv.prodComm ιA ιB) X

/-- **Lean-only:** Tensor products commute with the heterogeneous swap map.

Paper origin: `references/ldt-paper/inductive_step.tex:40-66`; this is the
matrix-index identity used to identify the two role-register sectors in the
heterogeneous symmetrization. -/
@[simp] theorem heterogeneousSwapDensity_opTensor {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    heterogeneousSwapDensity (opTensor A B) = opTensor B A := by
  ext i j
  rcases i with ⟨iB, iA⟩
  rcases j with ⟨jB, jA⟩
  simp [heterogeneousSwapDensity, opTensor]
  ring

theorem heterogeneousSwapDensity_nonneg {ιA ιB : Type*}
    [Finite ιA] [Finite ιB] {X : MIPStarRE.Quantum.Op (ιA × ιB)}
    (hX : 0 ≤ X) : 0 ≤ heterogeneousSwapDensity X :=
  MIPStarRE.Quantum.reindex_nonneg (Equiv.prodComm ιA ιB) hX

@[simp] theorem heterogeneousSwapDensity_mul {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιA × ιB)) :
    heterogeneousSwapDensity (X * Y) =
      heterogeneousSwapDensity X * heterogeneousSwapDensity Y := by
  classical
  unfold heterogeneousSwapDensity
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodComm ιA ιB)) X Y

@[simp] theorem swapDensity_localPairABBlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    swapDensity (localPairABBlock X) =
      localPairBABlock (heterogeneousSwapDensity X) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [swapDensity, localPairABBlock, localPairBABlock, heterogeneousSwapDensity]

@[simp] theorem swapDensity_localPairBABlock_heterogeneousSwapDensity {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    swapDensity (localPairBABlock (heterogeneousSwapDensity X)) =
      localPairABBlock X := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [swapDensity, localPairABBlock, localPairBABlock, heterogeneousSwapDensity]

theorem trace_localPairABBlock {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    Matrix.trace (localPairABBlock X) = Matrix.trace X := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Fintype.sum_sum_type, localPairABBlock, Matrix.of_apply,
    Finset.sum_const_zero, zero_add, add_zero]
  exact (Fintype.sum_prod_type'
    (f := fun i : ιA => fun j : ιB => X (i, j) (i, j))).symm

theorem trace_localPairBABlock {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    Matrix.trace (localPairBABlock X) = Matrix.trace X := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Fintype.sum_sum_type, localPairBABlock, Matrix.of_apply,
    Finset.sum_const_zero, zero_add, add_zero]
  exact (Fintype.sum_prod_type'
    (f := fun i : ιB => fun j : ιA => X (i, j) (i, j))).symm

theorem normalizedTrace_localPairABBlock {ιA ιB : Type*}
    [Fintype ιA] [Nonempty ιA] [Fintype ιB] [Nonempty ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.normalizedTrace (localPairABBlock X) =
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
        ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))) *
          MIPStarRE.Quantum.normalizedTrace X := by
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_localPairABBlock, Fintype.card_prod, Fintype.card_prod]
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
  rw [Nat.cast_mul]
  simp [Nat.cast_mul]
  ring_nf

theorem normalizedTrace_localPairBABlock {ιA ιB : Type*}
    [Fintype ιA] [Nonempty ιA] [Fintype ιB] [Nonempty ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    MIPStarRE.Quantum.normalizedTrace (localPairBABlock X) =
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
        ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))) *
          MIPStarRE.Quantum.normalizedTrace X := by
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_localPairBABlock, Fintype.card_prod, Fintype.card_prod]
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
  rw [Nat.cast_mul]
  simp [Nat.cast_mul]
  ring_nf

theorem normalizedTrace_heterogeneousSwapDensity {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.normalizedTrace (heterogeneousSwapDensity X) =
      MIPStarRE.Quantum.normalizedTrace X :=
  MIPStarRE.Quantum.normalizedTrace_reindex (Equiv.prodComm ιA ιB) X

@[simp] theorem rolePairProj_AB_mul_BA :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.A = 0 :=
  MIPStarRE.LDT.rolePairProj_AB_mul_BA

@[simp] theorem rolePairProj_BA_mul_AB :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.B = 0 :=
  MIPStarRE.LDT.rolePairProj_BA_mul_AB

/-- Place a direct-sum bipartite operator in a chosen pair of role sectors. -/
noncomputable def rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) :=
  Matrix.reindex (roleRegisterPairLocalEquiv ιA ιB)
    (roleRegisterPairLocalEquiv ιA ιB)
    (opTensor (rolePairProj rL rR) X)

theorem rolePairDirectSumCond_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    {X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)}
    (hX : 0 ≤ X) : 0 ≤ rolePairDirectSumCond rL rR X :=
  MIPStarRE.Quantum.reindex_nonneg (roleRegisterPairLocalEquiv ιA ιB)
    (opTensor_nonneg (MIPStarRE.LDT.rolePairProj_nonneg rL rR) hX)

theorem normalizedTrace_rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.normalizedTrace (rolePairDirectSumCond rL rR X) =
      (1 / 4 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
  have : Nonempty Role := ⟨Role.A⟩
  have : Nonempty (LocalCarrierSum ιA ιB) :=
    ⟨Sum.inl (Classical.choice inferInstance)⟩
  calc
    MIPStarRE.Quantum.normalizedTrace (rolePairDirectSumCond rL rR X)
      = MIPStarRE.Quantum.normalizedTrace (opTensor (rolePairProj rL rR) X) := by
          rw [rolePairDirectSumCond]
          exact MIPStarRE.Quantum.normalizedTrace_reindex
            (roleRegisterPairLocalEquiv ιA ιB) _
    _ = MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR) *
          MIPStarRE.Quantum.normalizedTrace X := by
            simpa using normalizedTrace_opTensor (rolePairProj rL rR) X
    _ = (1 / 4 : ℂ) * MIPStarRE.Quantum.normalizedTrace X := by
          rw [MIPStarRE.LDT.normalizedTrace_rolePairProj]

@[simp] theorem rolePairDirectSumCond_mul_same {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond rL rR X * rolePairDirectSumCond rL rR Y =
      rolePairDirectSumCond rL rR (X * Y) := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) Y) =
    (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) (X * Y))
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)]
  congr 1
  simp [opTensor_mul, rolePairProj, roleProj_mul_self]

/-- Distinct role-pair sectors of the direct-sum role register are orthogonal. -/
theorem rolePairDirectSumCond_mul_eq_zero_of_ne {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR sL sR : Role)
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB))
    (h : (rL, rR) ≠ (sL, sR)) :
    rolePairDirectSumCond rL rR X * rolePairDirectSumCond sL sR Y = 0 := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj sL sR) Y) = 0
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)]
  rw [opTensor_mul, rolePairProj_mul_eq_zero_of_ne rL rR sL sR h]
  simp [opTensor]

@[simp] theorem rolePairDirectSumCond_AB_mul_BA {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond Role.A Role.B X * rolePairDirectSumCond Role.B Role.A Y = 0 := by
  exact rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.B Role.A X Y (by decide)

@[simp] theorem rolePairDirectSumCond_BA_mul_AB {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond Role.B Role.A X * rolePairDirectSumCond Role.A Role.B Y = 0 := by
  exact rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.A Role.B X Y (by decide)

@[simp] theorem swapDensity_rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    swapDensity (rolePairDirectSumCond rL rR X) =
      rolePairDirectSumCond rR rL (swapDensity X) := by
  ext x y
  rcases x with ⟨⟨sL, iL⟩, ⟨sR, iR⟩⟩
  rcases y with ⟨⟨tL, jL⟩, ⟨tR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;> cases tL <;> cases tR <;>
    simp [swapDensity, rolePairDirectSumCond, rolePairProj, roleProj, opTensor,
      roleRegisterPairLocalEquiv]

/-- Normalizing scalar for the direct-sum heterogeneous role-register state. -/
noncomputable def roleRegisterDensityScale (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] :
    Error :=
  2 * ((Fintype.card (LocalCarrierSum ιA ιB) : Error) ^ (2 : ℕ)) /
    ((Fintype.card ιA : Error) * (Fintype.card ιB : Error))

theorem roleRegisterDensityScale_nonneg (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] :
    0 ≤ roleRegisterDensityScale ιA ιB := by
  unfold roleRegisterDensityScale
  positivity

/-- Heterogeneous role-register symmetrization of a two-space bipartite state.

The state lives on `Role × (ιA ⊕ ιB)` on each side.  Its occupied sectors are
`A/B`, carrying the original density in the `Sum.inl × Sum.inr` direct-sum
block, and `B/A`, carrying the swapped density in the `Sum.inr × Sum.inl` block.
The scalar compensates for normalized trace on the enlarged direct-sum carrier.
Normalization and the LDT goodness comparison are separate lemmas. -/
noncomputable def roleRegisterSymmState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) :
    QuantumState (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) where
  density :=
    roleRegisterDensityScale ιA ιB •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
    roleRegisterDensityScale ιA ιB •
      rolePairDirectSumCond Role.B Role.A
        (localPairBABlock (heterogeneousSwapDensity ψ.density))
  density_psd := add_nonneg
    (smul_nonneg (roleRegisterDensityScale_nonneg ιA ιB)
      (rolePairDirectSumCond_nonneg Role.A Role.B
        (localPairABBlock_nonneg ψ.density_psd)))
    (smul_nonneg (roleRegisterDensityScale_nonneg ιA ιB)
      (rolePairDirectSumCond_nonneg Role.B Role.A
        (localPairBABlock_nonneg (heterogeneousSwapDensity_nonneg ψ.density_psd))))

@[simp] theorem roleRegisterSymmState_density_fixed {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) :
    swapDensity (roleRegisterSymmState ψ).density =
      (roleRegisterSymmState ψ).density := by
  calc
    swapDensity (roleRegisterSymmState ψ).density
      = roleRegisterDensityScale ιA ιB •
          rolePairDirectSumCond Role.B Role.A
            (localPairBABlock (heterogeneousSwapDensity ψ.density)) +
        roleRegisterDensityScale ιA ιB •
          rolePairDirectSumCond Role.A Role.B
            (localPairABBlock ψ.density) := by
            let s : Error := roleRegisterDensityScale ιA ιB
            let A := rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density)
            let B := rolePairDirectSumCond Role.B Role.A
              (localPairBABlock (heterogeneousSwapDensity ψ.density))
            change swapDensity (s • A + s • B) = s • B + s • A
            rw [swapDensity_add]
            have hAB : swapDensity (s • A) = s • B := by
              change swapDensity ((s : ℂ) • A) = (s : ℂ) • B
              rw [swapDensity_smul]
              simp [A, B]
            have hBA : swapDensity (s • B) = s • A := by
              change swapDensity ((s : ℂ) • B) = (s : ℂ) • A
              rw [swapDensity_smul]
              simp [A, B]
            rw [hAB, hBA]
    _ = (roleRegisterSymmState ψ).density := by
          simp [roleRegisterSymmState, add_comm]

theorem roleRegisterSymmState_permInvState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) :
    PermInvState (roleRegisterSymmState ψ) :=
  permInvState_of_density_fixed (roleRegisterSymmState ψ)
    (roleRegisterSymmState_density_fixed ψ)

theorem roleRegisterSymmState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) :
    (roleRegisterSymmState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized roleRegisterSymmState
  rw [MIPStarRE.Quantum.normalizedTrace_add]
  change
    MIPStarRE.Quantum.normalizedTrace
        ((roleRegisterDensityScale ιA ιB : ℂ) •
          rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density)) +
      MIPStarRE.Quantum.normalizedTrace
        ((roleRegisterDensityScale ιA ιB : ℂ) •
          rolePairDirectSumCond Role.B Role.A
            (localPairBABlock (heterogeneousSwapDensity ψ.density))) = 1
  rw [MIPStarRE.Quantum.normalizedTrace_smul,
    MIPStarRE.Quantum.normalizedTrace_smul,
    normalizedTrace_rolePairDirectSumCond,
    normalizedTrace_rolePairDirectSumCond,
    normalizedTrace_localPairABBlock,
    normalizedTrace_localPairBABlock,
    normalizedTrace_heterogeneousSwapDensity, hψ]
  unfold roleRegisterDensityScale
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
  norm_num [Nat.cast_pow, Nat.cast_mul]
  field_simp [hA, hB]
  ring_nf

/-- Block-diagonal operator on `ιA ⊕ ιB`, with Alice's block in the
`Sum.inl` sector and Bob's block in the `Sum.inr` sector.

This is the matrix-level direct sum that will underlie symmetrized measurements
such as
`|0⟩⟨0| ⊗ A^A + |1⟩⟨1| ⊗ A^B` from
`references/ldt-paper/inductive_step.tex:55-59`. -/
noncomputable def localDirectSumBlock {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  Matrix.fromBlocks A 0 0 B

@[simp] theorem localDirectSumBlock_inl_inl {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i j : ιA) : localDirectSumBlock A B (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp] theorem localDirectSumBlock_inl_inr {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i : ιA) (j : ιB) : localDirectSumBlock A B (Sum.inl i) (Sum.inr j) = 0 :=
  rfl

@[simp] theorem localDirectSumBlock_inr_inl {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i : ιB) (j : ιA) : localDirectSumBlock A B (Sum.inr i) (Sum.inl j) = 0 :=
  rfl

@[simp] theorem localDirectSumBlock_inr_inr {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i j : ιB) : localDirectSumBlock A B (Sum.inr i) (Sum.inr j) = B i j :=
  rfl

@[simp] theorem localDirectSumBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    localDirectSumBlock (1 : MIPStarRE.Quantum.Op ιA) (1 : MIPStarRE.Quantum.Op ιB) = 1 := by
  simp [localDirectSumBlock]

@[simp] theorem localDirectSumBlock_zero {ιA ιB : Type*} :
    localDirectSumBlock (0 : MIPStarRE.Quantum.Op ιA) (0 : MIPStarRE.Quantum.Op ιB) = 0 := by
  simp [localDirectSumBlock]

/-- Direct-sum blocks are additive in the two diagonal blocks. -/
@[simp] theorem localDirectSumBlock_add {ιA ιB : Type*}
    (A₁ A₂ : MIPStarRE.Quantum.Op ιA) (B₁ B₂ : MIPStarRE.Quantum.Op ιB) :
    localDirectSumBlock A₁ B₁ + localDirectSumBlock A₂ B₂ =
      localDirectSumBlock (A₁ + A₂) (B₁ + B₂) := by
  simp [localDirectSumBlock, Matrix.fromBlocks_add]

@[simp] theorem localDirectSumBlock_conjTranspose {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    (localDirectSumBlock A B)ᴴ = localDirectSumBlock Aᴴ Bᴴ := by
  simp [localDirectSumBlock, Matrix.fromBlocks_conjTranspose]

@[simp] theorem localDirectSumBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A₁ A₂ : MIPStarRE.Quantum.Op ιA) (B₁ B₂ : MIPStarRE.Quantum.Op ιB) :
    localDirectSumBlock A₁ B₁ * localDirectSumBlock A₂ B₂ =
      localDirectSumBlock (A₁ * A₂) (B₁ * B₂) := by
  simp [localDirectSumBlock, Matrix.fromBlocks_multiply]

/-- A direct sum of positive semidefinite operators is positive semidefinite. -/
theorem localDirectSumBlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {A : MIPStarRE.Quantum.Op ιA} {B : MIPStarRE.Quantum.Op ιB}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ localDirectSumBlock A B := by
  classical
  let := Fintype.ofFinite ιA
  let := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hA hB ⊢
  rcases hA with ⟨C, hC⟩
  rcases hB with ⟨D, hD⟩
  refine ⟨localDirectSumBlock C D, ?_⟩
  have hC' : A = Cᴴ * C := hC
  have hD' : B = Dᴴ * D := hD
  change localDirectSumBlock A B = (localDirectSumBlock C D)ᴴ * localDirectSumBlock C D
  rw [localDirectSumBlock_conjTranspose, localDirectSumBlock_mul, ← hC', ← hD']

/-- Finite sums commute through direct-sum blocks.

This is the completeness calculation for block-diagonal measurements: if
Alice's and Bob's effects each sum to their local totals, then the direct-sum
effects sum to the direct sum of those totals. -/
theorem localDirectSumBlock_finset_sum {α ιA ιB : Type*} (s : Finset α)
    (A : α → MIPStarRE.Quantum.Op ιA) (B : α → MIPStarRE.Quantum.Op ιB) :
    ∑ a ∈ s, localDirectSumBlock (A a) (B a) =
      localDirectSumBlock (∑ a ∈ s, A a) (∑ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
      rw [localDirectSumBlock_add]

def roleBlockFamily {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    Role → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)
  | Role.A => A
  | Role.B => B

/-- The role-register block diagonal as a ring homomorphism. -/
private noncomputable def roleBlockRingHom {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB] :
    (Role → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) →+*
      MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB) := by
  classical
  exact
    (Matrix.reindexAlgEquiv ℂ ℂ
      (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)).toRingHom.comp
        (Matrix.blockDiagonalRingHom (LocalCarrierSum ιA ιB) Role ℂ)

/-- Role-blocked operator on `Role × (ιA ⊕ ιB)`.

The first block is used when the role register is `Role.A`; the second block is
used when the role register is `Role.B`. This is the direct-sum scaffold for the
paper's symmetrized measurements in `inductive_step.tex:55-59`. -/
noncomputable def roleBlock {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB) :=
  Matrix.reindex (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)
    (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)
    (Matrix.blockDiagonal (roleBlockFamily A B))

@[simp] theorem roleBlock_A {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.A, i) (Role.A, j) = A i j :=
  rfl

@[simp] theorem roleBlock_B {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.B, i) (Role.B, j) = B i j :=
  rfl

@[simp] theorem roleBlock_AB {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.A, i) (Role.B, j) = 0 :=
  rfl

@[simp] theorem roleBlock_BA {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.B, i) (Role.A, j) = 0 :=
  rfl

@[simp] theorem roleBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    roleBlock (1 : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) 1 = 1 := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp [Matrix.one_apply]

@[simp] theorem roleBlock_zero {ιA ιB : Type*} :
    roleBlock (0 : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) 0 = 0 := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

/-- Role-register blocks are additive in their two role sectors. -/
@[simp] theorem roleBlock_add {ιA ιB : Type*}
    (A₁ A₂ B₁ B₂ : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    roleBlock A₁ B₁ + roleBlock A₂ B₂ = roleBlock (A₁ + A₂) (B₁ + B₂) := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

@[simp] theorem roleBlock_conjTranspose {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    (roleBlock A B)ᴴ = roleBlock Aᴴ Bᴴ := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

@[simp] theorem roleBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A₁ A₂ B₁ B₂ : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    roleBlock A₁ B₁ * roleBlock A₂ B₂ = roleBlock (A₁ * A₂) (B₁ * B₂) := by
  classical
  change roleBlockRingHom (roleBlockFamily A₁ B₁) *
      roleBlockRingHom (roleBlockFamily A₂ B₂) =
    roleBlockRingHom (roleBlockFamily (A₁ * A₂) (B₁ * B₂))
  rw [← map_mul (roleBlockRingHom :
    (Role → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) →+*
      MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB))]
  congr
  ext r
  cases r <;> rfl

/-- A role block of positive semidefinite operators is positive semidefinite. -/
theorem roleBlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ roleBlock A B := by
  classical
  let := Fintype.ofFinite ιA
  let := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hA hB ⊢
  rcases hA with ⟨C, hC⟩
  rcases hB with ⟨D, hD⟩
  refine ⟨roleBlock C D, ?_⟩
  have hC' : A = Cᴴ * C := hC
  have hD' : B = Dᴴ * D := hD
  change roleBlock A B = (roleBlock C D)ᴴ * roleBlock C D
  rw [roleBlock_conjTranspose, roleBlock_mul, ← hC', ← hD']

/-- Finite sums commute through role-register blocks.

This is the role-sector analogue of `localDirectSumBlock_finset_sum` and is the main
completeness calculation for role-blocked measurements. -/
theorem roleBlock_finset_sum {α ιA ιB : Type*} (s : Finset α)
    (A B : α → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    ∑ a ∈ s, roleBlock (A a) (B a) =
      roleBlock (∑ a ∈ s, A a) (∑ a ∈ s, B a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
      rw [roleBlock_add]


end ProjStrat

end MIPStarRE.LDT

end

end LIDT


