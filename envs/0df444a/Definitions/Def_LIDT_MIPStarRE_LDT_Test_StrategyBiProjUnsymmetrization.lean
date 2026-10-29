-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
-- name    : LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:43:22.880732+00:00
-- url     : https://prove2.me/theorems/a8cab086-917e-47b1-bedc-f662702a8637
-- title:
--   LIDT definitions: LDT / Test / StrategyBiProjUnsymmetrization
-- statement:
--   This bundle extracts Alice's and Bob's local operators from the occupied principal blocks of a heterogeneous role-register operator. The extraction preserves positivity, order, sums, and completeness and supplies the embeddings needed to return role-register expectations to the original two-space strategy.
--
--   Principal definitions:
--   - `extractRoleRegisterAliceBlock`: The block indexed by the Alice role on both local factors.
--   - `extractRoleRegisterBobBlock`: The corresponding Bob-role block.
--   - `extractRoleRegisterAlice` and `extractRoleRegisterBob` in `SubMeas`: The extracted local submeasurements.
--   - `extractRoleRegisterAlice` and `extractRoleRegisterBob` in `Measurement`: The extracted complete measurements.
--   - `localPairABEmbedding` and `localPairBAEmbedding`: Embeddings of the two occupied role sectors.
--   - `rolePairSectorEmbedding`: The embedding of an arbitrary selected role pair.
--   - `roleRegisterRoleLocalBlock`: The block extraction over the local carrier sum.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean#L35-L449

-- Generated from MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
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

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.ProjStrat
end MIPStarRE.LDT.ProjStrat

/-!
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace ProjStrat

/-! ### Principal blocks of heterogeneous role-register operators -/

/-- Alice's principal block of an operator on the heterogeneous role-register
space, indexed by `(Role.A, Sum.inl _)`. -/
noncomputable def extractRoleRegisterAliceBlock {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op ιA :=
  Y.submatrix (fun i => (Role.A, Sum.inl i)) (fun i => (Role.A, Sum.inl i))

/-- Bob's principal block of an operator on the heterogeneous role-register
space, indexed by `(Role.B, Sum.inr _)`. -/
noncomputable def extractRoleRegisterBobBlock {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op ιB :=
  Y.submatrix (fun i => (Role.B, Sum.inr i)) (fun i => (Role.B, Sum.inr i))

@[simp] theorem extractRoleRegisterAliceBlock_apply {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) (i j : ιA) :
    extractRoleRegisterAliceBlock Y i j = Y (Role.A, Sum.inl i) (Role.A, Sum.inl j) :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_apply {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) (i j : ιB) :
    extractRoleRegisterBobBlock Y i j = Y (Role.B, Sum.inr i) (Role.B, Sum.inr j) :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_zero {ιA ιB : Type*} :
    extractRoleRegisterAliceBlock (ιA := ιA) (ιB := ιB) 0 = 0 :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_zero {ιA ιB : Type*} :
    extractRoleRegisterBobBlock (ιA := ιA) (ιB := ιB) 0 = 0 :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_add {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (X + Y) =
      extractRoleRegisterAliceBlock X + extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_add {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (X + Y) =
      extractRoleRegisterBobBlock X + extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_sub {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (X - Y) =
      extractRoleRegisterAliceBlock X - extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_sub {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (X - Y) =
      extractRoleRegisterBobBlock X - extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_smul {ιA ιB : Type*}
    (c : ℂ) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (c • Y) = c • extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_smul {ιA ιB : Type*}
    (c : ℂ) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (c • Y) = c • extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_finset_sum {α ιA ιB : Type*}
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (∑ a ∈ s, f a) =
      ∑ a ∈ s, extractRoleRegisterAliceBlock (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

@[simp] theorem extractRoleRegisterBobBlock_finset_sum {α ιA ιB : Type*}
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (∑ a ∈ s, f a) =
      ∑ a ∈ s, extractRoleRegisterBobBlock (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

@[simp] theorem extractRoleRegisterAliceBlock_univ_sum {α ιA ιB : Type*}
    [Fintype α] (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (∑ a, f a) =
      ∑ a, extractRoleRegisterAliceBlock (f a) := by
  exact extractRoleRegisterAliceBlock_finset_sum Finset.univ f

@[simp] theorem extractRoleRegisterBobBlock_univ_sum {α ιA ιB : Type*}
    [Fintype α] (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (∑ a, f a) =
      ∑ a, extractRoleRegisterBobBlock (f a) := by
  exact extractRoleRegisterBobBlock_finset_sum Finset.univ f

@[simp] theorem extractRoleRegisterAliceBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    extractRoleRegisterAliceBlock
      (1 : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

@[simp] theorem extractRoleRegisterBobBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    extractRoleRegisterBobBlock
      (1 : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Alice principal blocks preserve positive semidefiniteness. -/
theorem extractRoleRegisterAliceBlock_nonneg {ιA ιB : Type*}
    {Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hY : 0 ≤ Y) :
    0 ≤ extractRoleRegisterAliceBlock Y := by
  exact Matrix.nonneg_iff_posSemidef.mpr <|
    (Matrix.nonneg_iff_posSemidef.mp hY).submatrix (fun i => (Role.A, Sum.inl i))

/-- Bob principal blocks preserve positive semidefiniteness. -/
theorem extractRoleRegisterBobBlock_nonneg {ιA ιB : Type*}
    {Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hY : 0 ≤ Y) :
    0 ≤ extractRoleRegisterBobBlock Y := by
  exact Matrix.nonneg_iff_posSemidef.mpr <|
    (Matrix.nonneg_iff_posSemidef.mp hY).submatrix (fun i => (Role.B, Sum.inr i))

/-- Alice principal blocks are monotone for the matrix order. -/
theorem extractRoleRegisterAliceBlock_le {ιA ιB : Type*}
    {X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hXY : X ≤ Y) :
    extractRoleRegisterAliceBlock X ≤ extractRoleRegisterAliceBlock Y := by
  rw [Matrix.le_iff] at hXY ⊢
  simpa [extractRoleRegisterAliceBlock, extractRoleRegisterAliceBlock_sub,
    Matrix.submatrix_sub] using
    hXY.submatrix (fun i : ιA => (Role.A, Sum.inl i))

/-- Bob principal blocks are monotone for the matrix order. -/
theorem extractRoleRegisterBobBlock_le {ιA ιB : Type*}
    {X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hXY : X ≤ Y) :
    extractRoleRegisterBobBlock X ≤ extractRoleRegisterBobBlock Y := by
  rw [Matrix.le_iff] at hXY ⊢
  simpa [extractRoleRegisterBobBlock, extractRoleRegisterBobBlock_sub,
    Matrix.submatrix_sub] using
    hXY.submatrix (fun i : ιB => (Role.B, Sum.inr i))

end ProjStrat

namespace SubMeas

/-- Extract Alice's original local block from a submeasurement on the
heterogeneous role-register space. -/
noncomputable def extractRoleRegisterAlice {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) : SubMeas α ιA where
  outcome := fun a => ProjStrat.extractRoleRegisterAliceBlock (A.outcome a)
  total := ProjStrat.extractRoleRegisterAliceBlock A.total
  outcome_pos := fun a => ProjStrat.extractRoleRegisterAliceBlock_nonneg (A.outcome_pos a)
  sum_eq_total := (ProjStrat.extractRoleRegisterAliceBlock_univ_sum A.outcome).symm.trans
      (congrArg ProjStrat.extractRoleRegisterAliceBlock A.sum_eq_total)
  total_le_one := (ProjStrat.extractRoleRegisterAliceBlock_le A.total_le_one).trans_eq
      ProjStrat.extractRoleRegisterAliceBlock_one

/-- Extract Bob's original local block from a submeasurement on the
heterogeneous role-register space. -/
noncomputable def extractRoleRegisterBob {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) : SubMeas α ιB where
  outcome := fun a => ProjStrat.extractRoleRegisterBobBlock (A.outcome a)
  total := ProjStrat.extractRoleRegisterBobBlock A.total
  outcome_pos := fun a => ProjStrat.extractRoleRegisterBobBlock_nonneg (A.outcome_pos a)
  sum_eq_total := (ProjStrat.extractRoleRegisterBobBlock_univ_sum A.outcome).symm.trans
      (congrArg ProjStrat.extractRoleRegisterBobBlock A.sum_eq_total)
  total_le_one := (ProjStrat.extractRoleRegisterBobBlock_le A.total_le_one).trans_eq
      ProjStrat.extractRoleRegisterBobBlock_one

@[simp] theorem extractRoleRegisterAlice_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterAlice).outcome a =
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterBob_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterBob).outcome a =
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterAlice_total {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterAlice).total = ProjStrat.extractRoleRegisterAliceBlock A.total :=
  rfl

@[simp] theorem extractRoleRegisterBob_total {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterBob).total = ProjStrat.extractRoleRegisterBobBlock A.total :=
  rfl





end SubMeas

namespace Measurement

/-- Extract Alice's original local block from a measurement on the heterogeneous
role-register space. -/
noncomputable def extractRoleRegisterAlice {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) : Measurement α ιA where
  toSubMeas := A.toSubMeas.extractRoleRegisterAlice
  total_eq_one := (congrArg ProjStrat.extractRoleRegisterAliceBlock A.total_eq_one).trans
      ProjStrat.extractRoleRegisterAliceBlock_one

/-- Extract Bob's original local block from a measurement on the heterogeneous
role-register space. -/
noncomputable def extractRoleRegisterBob {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) : Measurement α ιB where
  toSubMeas := A.toSubMeas.extractRoleRegisterBob
  total_eq_one := (congrArg ProjStrat.extractRoleRegisterBobBlock A.total_eq_one).trans
      ProjStrat.extractRoleRegisterBobBlock_one

@[simp] theorem extractRoleRegisterAlice_toSubMeas {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterAlice).toSubMeas = A.toSubMeas.extractRoleRegisterAlice :=
  rfl

@[simp] theorem extractRoleRegisterBob_toSubMeas {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterBob).toSubMeas = A.toSubMeas.extractRoleRegisterBob :=
  rfl

@[simp] theorem extractRoleRegisterAlice_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterAlice).outcome a =
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterBob_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterBob).outcome a =
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a) :=
  rfl

end Measurement

namespace ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/





/-- The local-sector embedding selecting the Alice--Bob tensor summand. -/
 def localPairABEmbedding {ιA ιB : Type*} :
    ιA × ιB → LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB :=
  fun z => (Sum.inl z.1, Sum.inr z.2)

/-- The local-sector embedding selecting the Bob--Alice tensor summand. -/
 def localPairBAEmbedding {ιA ιB : Type*} :
    ιB × ιA → LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB :=
  fun z => (Sum.inr z.1, Sum.inl z.2)

/-- The role-sector embedding selecting the `rL,rR` block. -/
 def rolePairSectorEmbedding {ιA ιB : Type*} (rL rR : Role) :
    LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB →
      RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB :=
  fun z => ((rL, z.1), (rR, z.2))









 noncomputable def roleRegisterRoleLocalBlock {ιA ιB : Type*}
    (r : Role) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  Y.submatrix (fun i => (r, i)) (fun i => (r, i))































end ProjStrat

end MIPStarRE.LDT

end

end LIDT


