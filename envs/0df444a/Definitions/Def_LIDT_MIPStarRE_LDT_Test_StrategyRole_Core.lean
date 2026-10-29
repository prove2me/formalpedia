-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
-- name    : LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:36:33.215763+00:00
-- url     : https://prove2.me/theorems/d0769e35-253b-4ff8-8fda-f35e5f91909d
-- title:
--   LIDT definitions: LDT / Test / StrategyRole / Core
-- statement:
--   This bundle builds the classical role-register symmetrization used to pass from a two-space strategy to a swap-invariant strategy. Role projectors isolate the four role sectors, role-conditioned operators reindex local spaces into those sectors, and the symmetrized state carries the original and swapped states with the normalization correction.
--
--   Principal definitions:
--   - `roleProj`: The basis projector onto one of the two role labels.
--   - `roleCond`: Tensoring a local operator with a role projector to restrict it to a chosen role block.
--   - `roleRegisterPairLocalEquiv`: The canonical reassociation between role-register pairs and the original local-space tensor product.
--   - `rolePairProj`: The projector onto a specified pair of left and right role sectors.
--   - `rolePairCond`: Reindexes a bipartite local operator into role-register spaces and restricts it to a selected role pair.
--   - `classicalRoleSymmState`: The state formed from the original state in the $(A,B)$ sector and its swapped state in the $(B,A)$ sector, each scaled by two.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyRole/Core.lean#L27-L306

-- Generated from MIPStarRE/LDT/Test/StrategyRole/Core.lean by skeleton subtraction.
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

/-!
# Role-register tensor algebra for the low individual degree test

Role-register operators and strategy symmetrization infrastructure extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

@[expose] public section

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-! ### Role-register tensor algebra -/



/-- Basis projector onto the role sector `r`. -/
def roleProj (r : Role) : MIPStarRE.Quantum.Op Role :=
  Matrix.single r r (1 : ℂ)

/-- The basis projector onto a role sector is positive semidefinite. -/
lemma roleProj_nonneg (r : Role) : 0 ≤ roleProj r := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  let col : Matrix Role Unit ℂ := Matrix.single r () 1
  simpa [roleProj, col] using Matrix.posSemidef_self_mul_conjTranspose col

@[simp] lemma roleProj_mul_self (r : Role) :
    roleProj r * roleProj r = roleProj r := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj r i x * roleProj r x j) = roleProj r i j
  cases r <;> cases i <;> cases j <;> simp [roleProj]

@[simp] lemma roleProj_A_mul_B :
    roleProj Role.A * roleProj Role.B = 0 := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj Role.A i x * roleProj Role.B x j) = 0
  cases i <;> cases j <;> simp [roleProj]

@[simp] lemma roleProj_B_mul_A :
    roleProj Role.B * roleProj Role.A = 0 := by
  ext i j
  change
    Finset.sum ({Role.A, Role.B} : Finset Role)
      (fun x => roleProj Role.B i x * roleProj Role.A x j) = 0
  cases i <;> cases j <;> simp [roleProj]

/-- Tensor an operator with the role projector selecting the `r` block. -/
noncomputable def roleCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (Role × ι) :=
  opTensor (roleProj r) X



lemma roleCond_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) {X : MIPStarRE.Quantum.Op ι} (hX : 0 ≤ X) :
    0 ≤ roleCond r X :=
  opTensor_nonneg (roleProj_nonneg r) hX

@[simp] lemma roleCond_mul_same {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond r X * roleCond r Y = roleCond r (X * Y) := by
  simp [roleCond, opTensor_mul, roleProj_mul_self]

@[simp] lemma roleCond_A_mul_B {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond Role.A X * roleCond Role.B Y = 0 := by
  rw [roleCond, roleCond, opTensor_mul, roleProj_A_mul_B]
  simp [opTensor]

@[simp] lemma roleCond_B_mul_A {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : MIPStarRE.Quantum.Op ι) :
    roleCond Role.B X * roleCond Role.A Y = 0 := by
  rw [roleCond, roleCond, opTensor_mul, roleProj_B_mul_A]
  simp [opTensor]

lemma roleCond_finset_sum {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (r : Role) (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι) :
    Finset.sum s (fun a => roleCond r (f a)) = roleCond r (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [roleCond, opTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [roleCond, opTensor, Matrix.kronecker_add]

@[simp] lemma roleCond_one_sum {ι : Type*} [Fintype ι] [DecidableEq ι] :
    roleCond Role.A (1 : MIPStarRE.Quantum.Op ι) + roleCond Role.B 1 = 1 := by
  ext i j
  rcases i with ⟨ri, ii⟩
  rcases j with ⟨rj, ij⟩
  cases ri <;> cases rj <;> simp [roleCond, roleProj, opTensor, Matrix.one_apply]

/-- Reassociate the role and local-space indices for the role-register symmetrization. -/
def roleRegisterPairLocalEquiv (ι : Type*) :
    ((Role × Role) × (ι × ι)) ≃ ((Role × ι) × (Role × ι)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-- Basis projector onto a pair of role sectors. -/
noncomputable def rolePairProj (rL rR : Role) : MIPStarRE.Quantum.Op (Role × Role) :=
  opTensor (roleProj rL) (roleProj rR)

/-- Distinct role-pair sectors have zero product. -/
theorem rolePairProj_mul_eq_zero_of_ne (rL rR sL sR : Role)
    (h : (rL, rR) ≠ (sL, sR)) :
    rolePairProj rL rR * rolePairProj sL sR = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul]
  cases rL <;> cases rR <;> cases sL <;> cases sR <;>
    simp [opTensor] at h ⊢

/-- Orthogonal role-pair sectors `AB` and `BA` have zero product. -/
@[simp] theorem rolePairProj_AB_mul_BA :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.A = 0 := by
  exact rolePairProj_mul_eq_zero_of_ne Role.A Role.B Role.B Role.A (by decide)

/-- Orthogonal role-pair sectors `BA` and `AB` have zero product. -/
@[simp] theorem rolePairProj_BA_mul_AB :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.B = 0 := by
  exact rolePairProj_mul_eq_zero_of_ne Role.B Role.A Role.A Role.B (by decide)

/-- Reindex a bipartite local-space operator into the `(Role × ι)` local spaces and
restrict it to the selected role sector. -/
noncomputable def rolePairCond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι)) :=
  Matrix.reindex (roleRegisterPairLocalEquiv ι) (roleRegisterPairLocalEquiv ι)
    (opTensor (rolePairProj rL rR) X)

/-- The projection onto a pair of role sectors is positive semidefinite. -/
lemma rolePairProj_nonneg (rL rR : Role) : 0 ≤ rolePairProj rL rR :=
  opTensor_nonneg (roleProj_nonneg rL) (roleProj_nonneg rR)

private lemma rolePairCond_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rL rR : Role) {X : MIPStarRE.Quantum.Op (ι × ι)} (hX : 0 ≤ X) :
    0 ≤ rolePairCond rL rR X :=
  MIPStarRE.Quantum.reindex_nonneg (roleRegisterPairLocalEquiv ι)
    (opTensor_nonneg (rolePairProj_nonneg rL rR) hX)

@[simp] private lemma swapDensity_leftTensor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Op ι) :
    swapDensity (leftTensor (ι₂ := ι) M) = rightTensor (ι₁ := ι) M := by
  simpa [leftTensor, rightTensor, opTensor, Matrix.kronecker] using
    (swapDensity_opTensor M (1 : MIPStarRE.Quantum.Op ι))



private lemma swapDensity_nonneg {ι : Type*} [Finite ι]
    {X : MIPStarRE.Quantum.Op (ι × ι)} (hX : 0 ≤ X) :
    0 ≤ swapDensity X := by
  simpa [swapDensity_eq_reindex] using
    MIPStarRE.Quantum.reindex_nonneg (Equiv.prodComm ι ι) hX

/-- Classical role-register symmetrization of a bipartite state.

The `A/B` sector carries the original state, while the `B/A` sector carries the
swapped state. The scalar `2` on each occupied role sector compensates for the
normalized-trace convention on the enlarged ambient space. -/
noncomputable def classicalRoleSymmState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) :
    QuantumState ((Role × ι) × (Role × ι)) where
  density :=
    (2 : Error) • rolePairCond Role.A Role.B ψ.density +
      (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density)
  density_psd := by
    exact add_nonneg
      (smul_nonneg zero_le_two
        (rolePairCond_nonneg Role.A Role.B ψ.density_psd))
      (smul_nonneg zero_le_two
        (rolePairCond_nonneg Role.B Role.A (swapDensity_nonneg ψ.density_psd)))

@[simp] theorem classicalRoleSymmState_density_fixed {ι : Type*}
    [Fintype ι] [DecidableEq ι] (ψ : QuantumState (ι × ι)) :
    swapDensity (classicalRoleSymmState ψ).density = (classicalRoleSymmState ψ).density := by
  have hrolePair (rL rR : Role) (X : MIPStarRE.Quantum.Op (ι × ι)) :
      swapDensity (rolePairCond rL rR X) = rolePairCond rR rL (swapDensity X) := by
    ext x y
    rcases x with ⟨⟨sL, iL⟩, ⟨sR, iR⟩⟩
    rcases y with ⟨⟨tL, jL⟩, ⟨tR, jR⟩⟩
    cases rL <;> cases rR <;> cases sL <;> cases sR <;> cases tL <;> cases tR <;>
      simp [swapDensity, rolePairCond, rolePairProj, roleProj, opTensor, roleRegisterPairLocalEquiv]
  calc
    swapDensity (classicalRoleSymmState ψ).density
      = (2 : Error) • swapDensity (rolePairCond Role.A Role.B ψ.density) +
          (2 : Error) • swapDensity
            (rolePairCond Role.B Role.A (swapDensity ψ.density)) := by
              ext x y
              rcases x with ⟨iL, iR⟩
              rcases y with ⟨jL, jR⟩
              simp [classicalRoleSymmState, swapDensity]
    _ = (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density) +
          (2 : Error) • rolePairCond Role.A Role.B (swapDensity (swapDensity ψ.density)) := by
              simp [hrolePair]
    _ = (2 : Error) • rolePairCond Role.B Role.A (swapDensity ψ.density) +
          (2 : Error) • rolePairCond Role.A Role.B ψ.density := by
              simp
    _ = (classicalRoleSymmState ψ).density := by
          simp [classicalRoleSymmState, add_comm]

/-- The normalized trace of a two-role sector projection is `1 / 4`. -/
lemma normalizedTrace_rolePairProj (rL rR : Role) :
    MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR) = (1 / 4 : ℂ) := by
  have hRole : Fintype.card Role = 2 := by decide
  calc
    MIPStarRE.Quantum.normalizedTrace (rolePairProj rL rR)
      = MIPStarRE.Quantum.normalizedTrace (roleProj rL) *
          MIPStarRE.Quantum.normalizedTrace (roleProj rR) :=
            normalizedTrace_opTensor (roleProj rL) (roleProj rR)
    _ = (1 / 2 : ℂ) * (1 / 2 : ℂ) := by
          cases rL <;> cases rR <;>
            simp [MIPStarRE.Quantum.normalizedTrace, roleProj, hRole]
    _ = (1 / 4 : ℂ) := by norm_num







theorem permInvState_of_density_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density) :
    PermInvState ψ := by
  refine ⟨hfix, ?_⟩
  intro M
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * leftTensor (ι₂ := ι) M)
      = MIPStarRE.Quantum.normalizedTrace
          (swapDensity (ψ.density * leftTensor (ι₂ := ι) M)) := by
            symm
            exact normalizedTrace_swapDensity _
    _ = MIPStarRE.Quantum.normalizedTrace
          (swapDensity ψ.density * swapDensity (leftTensor (ι₂ := ι) M)) := by
            rw [swapDensity_mul]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * rightTensor (ι₁ := ι) M) := by
            rw [hfix, swapDensity_leftTensor]
















end MIPStarRE.LDT

end

end LIDT


