-- Prove2me | Definitions.Def_OAIQ084L012
-- name    : OAIQ084L012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:27:39.492992+00:00
-- url     : https://prove2.me/theorems/b3fae6fc-ba52-42f2-9242-ee851bf24ce8
-- title:
--   Definitions bundle OAIQ084L012 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 107 declarations of OpenAI's Lean: 92 definitions and 15 theorems. The definitions and types are `OAI.LaughlinFock.collectedFourData_9_7_24`, `OAI.LaughlinFock.collectedFourData_9_7_25`, `OAI.LaughlinFock.collectedFourData_9_7_26`, `OAI.LaughlinFock.collectedFourData_9_7_28`, `OAI.LaughlinFock.collectedFourData_9_7_29`, `OAI.LaughlinFock.collectedFourData_9_7_3`, `OAI.LaughlinFock.collectedFourData_9_7_30`, `OAI.LaughlinFock.collectedFourData_9_7_31`, `OAI.LaughlinFock.collectedFourData_9_7_32`, `OAI.LaughlinFock.collectedFourData_9_7_33`, `OAI.LaughlinFock.collectedFourData_9_7_34`, `OAI.LaughlinFock.collectedFourData_9_7_35`, `OAI.LaughlinFock.collectedFourData_9_7_36`, `OAI.LaughlinFock.collectedFourData_9_7_37`, `OAI.LaughlinFock.collectedFourData_9_7_38`, `OAI.LaughlinFock.collectedFourData_9_7_39`, `OAI.LaughlinFock.collectedFourData_9_7_4`, `OAI.LaughlinFock.collectedFourData_9_7_40`, `OAI.LaughlinFock.collectedFourData_9_7_41`, `OAI.LaughlinFock.collectedFourData_9_7_42`, `OAI.LaughlinFock.collectedFourData_9_7_43`, `OAI.LaughlinFock.collectedFourData_9_7_5`, `OAI.LaughlinFock.collectedFourData_9_7_6`, `OAI.LaughlinFock.collectedFourData_9_7_7`, `OAI.LaughlinFock.collectedFourData_9_7_8`, `OAI.LaughlinFock.collectedFourData_9_7_9`, `OAI.LaughlinFock.copyMatrixData`, `OAI.LaughlinFock.covarianceSubgroup`, `OAI.LaughlinFock.creator`, `OAI.LaughlinFock.cubeLower`, `OAI.LaughlinFock.cubeRaise`, `OAI.LaughlinFock.factorialMode`, `OAI.LaughlinFock.fastFourGram`, `OAI.LaughlinFock.fastHighestEntry`, `OAI.LaughlinFock.fastHighestTerm`, `OAI.LaughlinFock.firstFourCopy`, `OAI.LaughlinFock.fourBodyTerm`, `OAI.LaughlinFock.fourCopyAllowance`, `OAI.LaughlinFock.fourHighestCache_10`, `OAI.LaughlinFock.fourHighestCache_10_0` and 52 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinFock_AllowanceOrbit`, `LaughlinFock_Certificate02`, `LaughlinFock_Certificate04`, `LaughlinFock_Certificate06`, `LaughlinFock_Certificate09`, `LaughlinFock_Certificate10`, `LaughlinFock_Certificate11`, `LaughlinFock_Certificate12`, `LaughlinFock_Certificate13`, `LaughlinFock_Certificate14`, `LaughlinFock_Certificate15`, `LaughlinFock_Certificate16`, `LaughlinFock_Certificate17`, `LaughlinFock_CopyVectors`, `LaughlinFock_FastWedge`, `LaughlinFock_FermionOperators`, `LaughlinFock_FiniteCoupling`, `LaughlinFock_FourCoefficients`, `LaughlinFock_FourHighest`, `LaughlinFock_IntegerFour`, `LaughlinFock_LDL`, `LaughlinFock_LadderCalculus`, `LaughlinFock_LocalEnergy`, `LaughlinFock_NormalOrdering`, `LaughlinFock_RationalWedge`, `LaughlinFock_Rotations`, `LaughlinFock_Sparse0927`, `LaughlinFock_Sparse0928`, `LaughlinFock_Sparse0929`, `LaughlinFock_Sparse0930`, `LaughlinFock_SwapCompression`, `LaughlinFock_TensorBasis`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L000` and `OAIQ084L001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ084L022`, `OAIQ084L023`, `OAIQ084L024`, `OAIQ084L025`, `OAIQ084L026`, `OAIQ084L027`, `OAIQ084L028`, `OAIQ084L029`, `OAIQ084L030`, `OAIQ084L031`, `OAIQ084L032`, `OAIQ084L033`, `OAIQ084L034`, `OAIQ084L035`, `OAIQ084L036`, `OAIQ084L037`, `OAIQ084L038`, `OAIQ084L039`, `OAIQ084L040`, `OAIQ084L041` and `OAIQ084L042`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L000
import Definitions.Def_OAIQ084L001

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FermionOperators
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fermion Operators. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial


def creator (Q : ℕ) (j : Orbital Q) : FockMatrix Q := fun A B =>
  if j ∉ B ∧ A = insert j B then fermionSign j B else 0


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LocalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local Energy. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology

def localDeltaInv (L Q : ℕ) : FockMatrix L :=
  occupationDiagonalInv L (fun j => (modeScale Q j.val : ℂ))

open Filter Topology

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NormalOrdering
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Ordering. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker
open scoped Matrix ComplexOrder Kronecker BigOperators



def fourBodyTerm (Q : ℕ) : FockMatrix Q :=
  ∑ p ∈ Finset.range (2*Q-1), ∑ r ∈ Finset.range (2*Q-1),
    (pairAnnihilator Q p * pairAnnihilator Q r)ᴴ *
      (pairAnnihilator Q p * pairAnnihilator Q r)


def threeWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 3) (PairLabel Q × Orbital Q) ℂ :=
  fun S pj => annihilatorVector Q 3
    (annihilator Q pj.2 * pairAnnihilator Q pj.1.val) S

 
def fourWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 4) (PairLabel Q × PairLabel Q) ℂ :=
  fun S pr => annihilatorVector Q 4
    (pairAnnihilator Q pr.2.val * pairAnnihilator Q pr.1.val) S

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteCoupling
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology



theorem highestWeight_zero (n m z p : ℕ) (hp : z < p) :
    highestWeight n m z p = 0 := by
  simp [highestWeight, Nat.choose_eq_zero_of_lt hp]

theorem highestCoefficient_zero (n m z p : ℕ) (hp : z < p) :
    highestCoefficient n m z p = 0 := by
  simp [highestCoefficient, highestWeight_zero n m z p hp]

theorem highestTotal_pos {n m z : ℕ} (hz : z ≤ n) : 0 < highestTotal n m z := by
  unfold highestTotal
  apply Finset.sum_pos'
  · exact fun _ _ => Nat.zero_le _
  · refine ⟨0, by simp, ?_⟩
    simpa [highestWeight] using Nat.descFactorial_pos.mpr hz

theorem highestCoefficient_sq (n m z p : ℕ) :
    highestCoefficient n m z p ^ 2 = (highestWeight n m z p : ℝ) / highestTotal n m z := by
  rw [highestCoefficient, mul_pow, ← pow_mul, mul_comm (z-p) 2, pow_mul]
  norm_num only [neg_sq, one_pow, one_mul]
  exact Real.sq_sqrt (by positivity)

 

theorem highestCoefficient_norm {n m z : ℕ} (hz : z ≤ n) :
    ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 = 1 := by
  simp_rw [highestCoefficient_sq]
  rw [← Finset.sum_div]
  have ht : (∑ p ∈ Finset.range (z+1), (highestWeight n m z p : ℝ)) =
      (highestTotal n m z : ℝ) := by simp [highestTotal]
  rw [ht, div_self (by exact_mod_cast (highestTotal_pos (m := m) hz).ne')]

 
theorem highestWeight_adjacent {n m z p : ℕ} (hz : z ≤ n) (hp : p < z) :
    highestWeight n m z (p+1) * ((p+1)*(n-p)) =
      highestWeight n m z p * ((z-p)*(m-z+p+1)) := by
  have hnp : n-p = (n-(p+1))+1 := by omega
  have hzp : z-p = (z-(p+1))+1 := by omega
  have hnfall : (n-p).descFactorial (z-p) =
      (n-p) * (n-(p+1)).descFactorial (z-(p+1)) := by
    rw [hnp, hzp, Nat.succ_descFactorial_succ]
  have hmfall : (m-z+(p+1)).descFactorial (p+1) =
      (m-z+p+1) * (m-z+p).descFactorial p := by
    rw [show m-z+(p+1) = (m-z+p)+1 by omega, Nat.succ_descFactorial_succ]
  unfold highestWeight
  rw [hnfall, hmfall]
  have hch := Nat.choose_succ_right_eq z p
  calc
    _ = (z.choose (p+1) * (p+1)) * (n-p) *
        (n-(p+1)).descFactorial (z-(p+1)) *
        ((m-z+p+1) * (m-z+p).descFactorial p) := by ring
    _ = _ := by rw [hch]; ring

 

theorem highestCoefficient_raising {n m z p : ℕ} (hz : z ≤ n) (hp : p < z) :
    highestCoefficient n m z (p+1) * Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) +
      highestCoefficient n m z p * Real.sqrt ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ) = 0 := by
  have he : (highestWeight n m z (p+1) : ℝ) / highestTotal n m z *
      ((p+1 : ℕ) * (n-p : ℕ) : ℝ) =
      (highestWeight n m z p : ℝ) / highestTotal n m z *
      ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ) := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (highestWeight_adjacent (m := m) hz hp)
    push_cast at h
    simpa only [div_mul_eq_mul_div, Nat.cast_add, Nat.cast_one] using congrArg (fun a : ℝ => a / highestTotal n m z) h
  have hs :
      Real.sqrt ((highestWeight n m z (p+1) : ℝ) / highestTotal n m z) *
        Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) =
      Real.sqrt ((highestWeight n m z p : ℝ) / highestTotal n m z) *
        Real.sqrt ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ) := by
    calc
      _ = Real.sqrt ((highestWeight n m z (p+1) : ℝ) / highestTotal n m z *
          ((p+1 : ℕ) * (n-p : ℕ) : ℝ)) := (Real.sqrt_mul (by positivity) _).symm
      _ = _ := congrArg Real.sqrt he
      _ = _ := Real.sqrt_mul (by positivity) _
  have hpar : (-1 : ℝ)^(z-p) = -((-1 : ℝ)^(z-(p+1))) := by
    rw [show z-p = z-(p+1)+1 by omega, pow_succ]
    ring
  unfold highestCoefficient
  rw [hpar]
  calc
    _ = (-1 : ℝ)^(z-(p+1)) *
        (Real.sqrt ((highestWeight n m z (p+1) : ℝ) / highestTotal n m z) *
            Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) -
         Real.sqrt ((highestWeight n m z p : ℝ) / highestTotal n m z) *
            Real.sqrt ((z-p : ℕ) * (m-z+p+1 : ℕ) : ℝ)) := by ring
    _ = 0 := by rw [hs, sub_self, mul_zero]


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCoefficients
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Coefficients. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology

 
theorem coupledCoefficient_left_support {n m z : ℕ} (hz : z ≤ n)
    (k p : ℕ) (hp : n < p) : coupledCoefficient n m z k p = 0 := by
  induction k generalizing p with
  | zero => exact highestCoefficient_zero _ _ _ _ (by omega)
  | succ k ih =>
    rw [coupledCoefficient, ih p hp]
    simp only [mul_zero, add_zero]
    by_cases he : p = n+1
    · rw [he]
      have he' : (n : ℝ)+1-(n+1 : ℕ) = 0 := by push_cast; ring
      simp only [he', mul_zero, Real.sqrt_zero, zero_mul]
      split_ifs <;> simp
    · rw [ite_eq_right (by omega : p ≠ 0), ih (p-1) (by omega)]
      simp

 

theorem coupledCoefficient_right_support {n m z : ℕ} (hz : z ≤ m)
    (k p : ℕ) (hp : m+p < z+k) : coupledCoefficient n m z k p = 0 := by
  induction k generalizing p with
  | zero => omega
  | succ k ih =>
    rw [coupledCoefficient]
    have hfirst : (if p = 0 then 0 else
        Real.sqrt ((p : ℝ)*((n : ℝ)+1-p)) * coupledCoefficient n m z k (p-1)) = 0 := by
      split_ifs with hp0
      · rfl
      · rw [ih (p-1) (by omega), mul_zero]
    rw [hfirst, zero_add]
    by_cases he : m+p = z+k
    · have he' : (m : ℝ)+p-z-k = 0 := by exact_mod_cast sub_eq_zero.mpr (show (m+p : ℤ)-z=k by omega)
      simp [he']
    · rw [ih p (by omega)]
      simp



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LadderCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ladder Calculus. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators



theorem spinStep_sq {n p : ℕ} (hp : p ≤ n+1) :
    spinStep n p ^ 2 = (p : ℝ)*((n : ℝ)+1-p) := by
  apply Real.sq_sqrt
  apply mul_nonneg (Nat.cast_nonneg _)
  have h : (p : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hp
  linarith

theorem spinStep_sq_sub {n p : ℕ} (hp : p ≤ n) :
    spinStep n (p+1)^2 - spinStep n p^2 = (n : ℝ)-2*p := by
  rw [spinStep_sq (by omega : p+1 ≤ n+1), spinStep_sq (by omega : p ≤ n+1)]
  push_cast
  ring

theorem spinStep_pos {n p : ℕ} (hp0 : 0 < p) (hpn : p ≤ n) :
    0 < spinStep n p := by
  apply Real.sqrt_pos.mpr
  apply mul_pos (by exact_mod_cast hp0)
  have h : (p : ℝ) ≤ n := by exact_mod_cast hpn
  linarith

theorem spinStep_sum_adjoint (n : ℕ) (f g : ℕ → ℝ) :
    (∑ p ∈ Finset.range (n+1), (spinStep n p * f (p-1)) * g p) =
      ∑ p ∈ Finset.range (n+1), f p * (spinStep n (p+1) * g (p+1)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [spinStep_zero, zero_mul, spinStep_last, mul_zero, add_zero, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro p _
  ring



theorem spinStep_succ {n p : ℕ} (hp : p ≤ n) :
    spinStep n (p+1) = Real.sqrt ((p+1 : ℕ) * (n-p : ℕ) : ℝ) := by
  unfold spinStep
  rw [Nat.cast_sub hp]
  congr 2
  push_cast
  ring



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TensorBasis
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators


theorem coupledIndex_card (n m : ℕ) :
    Fintype.card (CoupledIndex n m) = (n+1)*(m+1) := by
  have hc : (Fintype.card (CoupledIndex n m) : ℤ) = ((n : ℤ)+1)*((m : ℤ)+1) := by
    simp only [CoupledIndex, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ = ∑ z : Fin (min n m+1), ((n : ℤ)+m+1-2*z.val) := by
        apply Finset.sum_congr rfl
        intro z _
        have hz : 2*z.val ≤ n+m := by
          have h := z.isLt
          have h₁ := min_le_left n m
          have h₂ := min_le_right n m
          omega
        rw [Nat.cast_add, Nat.cast_sub hz]
        push_cast
        ring
      _ = ((min n m+1 : ℕ) : ℤ)*((n : ℤ)+m+1) -
          ((min n m+1 : ℕ) : ℤ)*(((min n m+1 : ℕ) : ℤ)-1) := by
        rw [Fin.sum_univ_eq_sum_range (fun z : ℕ => (n : ℤ)+m+1-2*z) (min n m+1), sum_affine_integer]
      _ = _ := by
        rcases le_total n m with h | h
        · rw [min_eq_left h]
          push_cast
          ring
        · rw [min_eq_right h]
          push_cast
          ring
  exact_mod_cast hc

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SwapCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swap Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

def cubeLower (Q : ℕ) (f : CubeVector) : CubeVector := fun i j k =>
  spinStep Q i * f (i-1) j k + spinStep Q j * f i (j-1) k +
    spinStep Q k * f i j (k-1)

def cubeRaise (Q : ℕ) (f : CubeVector) : CubeVector := fun i j k =>
  spinStep Q (i+1) * f (i+1) j k + spinStep Q (j+1) * f i (j+1) k +
    spinStep Q (k+1) * f i j (k+1)



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CopyVectors
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Copy Vectors. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def wideFourWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 4) (FourUncoupled Q) ℂ := fun A b =>
  annihilatorVector Q 4
    (annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val) A

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Rotations
attribute [-instance] _root_.OAI.LaughlinFock.rotationHaar_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory Topology

section Simultaneous
variable {J : Type*} (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]



def covarianceSubgroup {i j : J}
    (L : Matrix (I i) (I i) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ) :
    Subgroup (UnitaryFamily I) where
  carrier := {g | ∀ M, L (unitaryConjugation (g i) M) = unitaryConjugation (g j) (L M)}
  one_mem' := by intro M; simp only [Pi.one_apply, unitaryConjugation_one]
  mul_mem' := by
    intro g h hg hh M
    change ∀ M, L (unitaryConjugation (g i) M) = unitaryConjugation (g j) (L M) at hg
    change ∀ M, L (unitaryConjugation (h i) M) = unitaryConjugation (h j) (L M) at hh
    simp only [Pi.mul_apply, unitaryConjugation_mul, hg, hh]
  inv_mem' := by
    intro g hg M
    have h := congrArg (unitaryConjugation (g j)⁻¹)
      (hg (unitaryConjugation (g i)⁻¹ M))
    simpa only [Pi.inv_apply, ← unitaryConjugation_mul, mul_inv_cancel, inv_mul_cancel,
      unitaryConjugation_one] using h.symm

end Simultaneous

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_AllowanceOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Allowance Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open Filter Topology



def fourCopyAllowance (Q : ℕ) : FockMatrix Q :=
  ((2*Q-1 : ℕ) : ℂ) • ∑ D ∈ Finset.Icc 1 23,
    fockAverage Q (∑ r : CopyLabel D,
      (highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D r)



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalWedge
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def rationalWordVacuum {Q : ℕ} : List (Orbital Q) → Occupation Q → ℚ
  | [], A => if A=∅ then 1 else 0
  | x::xs, A => if x∈A then
      rationalWordVacuum xs (A.erase x) * (-1)^((A.filter (· < x)).card) else 0

def factorialMode (Q : ℕ) (a : Orbital Q) : ℂ :=
  (Real.sqrt (a.val.factorial : ℝ) : ℂ)

def rationalHighestTerm (D : ℕ) (r : CopyLabel D) (p j k x y : ℕ) : ℚ :=
  if x+y=p+1 then
    rationalCopyPolynomial D D r.val.val p j k * ((x:ℚ)-(y:ℚ)) *
      p.factorial * j.factorial * k.factorial
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastWedge
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def fastHighestTerm (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) : ℚ :=
  if x<y ∧ j<k ∧ (x.val+y.val-1)+j.val+k.val=D then
    rationalHighestTerm D r (x.val+y.val-1) j.val k.val x.val y.val *
      rationalWordVacuum [x,y,j,k] A
  else 0

def fastHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ j ∈ A, ∑ k ∈ A, ∑ x ∈ A, ∑ y ∈ A, fastHighestTerm D r A x y j k

end LaughlinFock
end

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fastFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A ∈ highestFourOccupations D,
    2 * fastHighestEntry D r A * fastHighestEntry D s A /
      (2^(2*D) * occupationFactorial A)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerFour
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def integerHighestTerm (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) : ℚ :=
  if x<y ∧ j<k ∧ (x.val+y.val-1)+j.val+k.val=D then
    (integerCopyPolynomial D D r.val.val (x.val+y.val-1) j.val k.val : ℚ) *
      ((x.val:ℚ)-(y.val:ℚ)) * (x.val+y.val-1).factorial * j.val.factorial * k.val.factorial *
      rationalWordVacuum [x,y,j,k] A
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LDL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L D L. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def copyMatrixData (D : ℕ) (xs : List (List ℚ)) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  fun r s => ((xs[r.val.val/2]?.getD [])[s.val.val/2]?).getD 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate02. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourHighestCache_2 : List (Occupation 24 × List ℚ) := [

]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate04. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourHighestCache_4 : List (Occupation 24 × List ℚ) := [

]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate06
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate06. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourHighestCache_6 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,4}, [0, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0927
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0927. -/
namespace LaughlinFock

def collectedFourData_9_7_3 : List CollectedFourTerm := [
  ⟨1, 7, 1, 0, 8, 1, 1262977800432316104180204649005178390448386867200000⟩,
  ⟨1, 7, 1, 1, 7, 1, 13244462615428263752606675032861053703083471667200000⟩,
  ⟨1, 7, 2, 1, 8, 1, -7283004124613573838119194244371124947577418547200000⟩,
  ⟨1, 7, 1, 2, 6, 1, 15705470326546771752898422037695822624862293196800000⟩,
  ⟨1, 7, 2, 2, 7, 1, -8852805934151098453714227467293191628453733990400000⟩,
  ⟨1, 7, 3, 2, 8, 1, -1861996765967856110240166057166861758986452992000000⟩,
  ⟨1, 7, 1, 3, 5, 1, 12975141378177806052780584288415183662826179788800000⟩,
  ⟨1, 7, 2, 3, 6, 1, -3516802716055758181255225729947131671757193216000000⟩,
  ⟨1, 7, 3, 3, 7, 1, -4649200036585737939094999687069841181732608409600000⟩,
  ⟨1, 7, 4, 3, 8, 1, -900271934637045857190639738963825952766400921600000⟩,
  ⟨1, 7, 1, 4, 4, 1, -14614088736890430931851266241841805027045906841600000⟩,
  ⟨1, 7, 2, 4, 5, 1, -1633270813361224184198111326302191509382470041600000⟩,
  ⟨1, 7, 3, 4, 6, 1, -10679270835122568328250473466442065233641367142400000⟩,
  ⟨1, 7, 4, 4, 7, 1, -2051526732371545340928046728662867984892139929600000⟩,
  ⟨1, 7, 5, 4, 8, 1, 2228466737644481109377247834458294673205100544000000⟩,
  ⟨1, 7, 1, 5, 3, 1, -27909185213976263616393475839574324099572930969600000⟩,
  ⟨1, 7, 2, 5, 4, 1, 8659982914898238047088298463818903173050086195200000⟩,
  ⟨1, 7, 3, 5, 5, 1, -3509763466220710603288942706973135474472570060800000⟩,
  ⟨1, 7, 4, 5, 6, 1, 1881821962723966326777047953476592206466567372800000⟩,
  ⟨1, 7, 5, 5, 7, 1, -75808959512985661394569965766880503032446976000000⟩,
  ⟨1, 7, 6, 5, 8, 1, 627784522993326112635925428344323598146181529600000⟩,
  ⟨1, 7, 1, 6, 2, 1, 69547416784468498693099004509807211260336825958400000⟩,
  ⟨1, 7, 2, 6, 3, 1, 4369673704216692069152145100076300714171695104000000⟩,
  ⟨1, 7, 3, 6, 4, 1, 16559097757232333568841911442706685273318830899200000⟩,
  ⟨1, 7, 4, 6, 5, 1, -3053413549715916565343013062879167426574313062400000⟩,
  ⟨1, 7, 5, 6, 6, 1, 721078486565799304760641442451931187782877184000000⟩,
  ⟨1, 7, 6, 6, 7, 1, 592877660186398307975010140289509272498628198400000⟩,
  ⟨1, 7, 7, 6, 8, 1, 108402836819584331748477880915989345063036518400000⟩,
  ⟨1, 7, 1, 7, 1, 1, -199015117745155383362253585606832805748647814758400000⟩,
  ⟨1, 7, 2, 7, 2, 1, -21134335478463997922980429409975612063734982246400000⟩,
  ⟨1, 7, 3, 7, 3, 1, -29511750037059648961190161777620779115954674073600000⟩,
  ⟨1, 7, 4, 7, 4, 1, -12627737874085928162949261878834159743910333644800000⟩,
  ⟨1, 7, 5, 7, 5, 1, -815467915625731554431332198522909661010591744000000⟩,
  ⟨1, 7, 6, 7, 6, 1, -641683258367879873356937486066655992255348736000000⟩,
  ⟨1, 7, 7, 7, 7, 1, -38313100864753686042657229615212995670127411200000⟩,
  ⟨1, 7, 8, 7, 8, 1, -146861931612840130898379838896712492913786880000000⟩
]

def collectedFourData_9_7_4 : List CollectedFourTerm := [
  ⟨1, 8, 0, 0, 7, 2, -6035629236369518737109976906039557613786287308800000⟩,
  ⟨1, 8, 1, 0, 8, 2, -694499489856916957923482600531022841388413747200000⟩,
  ⟨1, 8, 0, 1, 6, 2, -759351827759896028992159870823426212304938598400000⟩,
  ⟨1, 8, 1, 1, 7, 2, -7283004124613573838119194244371124947577418547200000⟩,
  ⟨1, 8, 2, 1, 8, 2, 2002427377361100839094922305653740351881058713600000⟩,
  ⟨1, 8, 0, 2, 5, 2, 3672566024041524166162858408401067156340893286400000⟩,
  ⟨1, 8, 1, 2, 6, 2, -8636288876982693765557541923967837022827891916800000⟩,
  ⟨1, 8, 2, 2, 7, 2, 2434036925655256304906091537741930713826145075200000⟩,
  ⟨1, 8, 3, 2, 8, 2, 341298108759910970489581992457920204729483264000000⟩,
  ⟨1, 8, 0, 3, 4, 2, -2332291169474980664478070748590701384087424204800000⟩,
  ⟨1, 8, 1, 3, 5, 2, -7134906935720743122383733418432305899607215308800000⟩,
  ⟨1, 8, 2, 3, 6, 2, 966928195963581773189887740045537717736439808000000⟩,
  ⟨1, 8, 3, 3, 7, 2, 852183638948712195101907273699682482277004083200000⟩,
  ⟨1, 8, 4, 3, 8, 2, 123762745300018243443892817483661778312652390400000⟩,
  ⟨1, 8, 0, 4, 3, 2, -8950744880540562526445642743450990431390243225600000⟩,
  ⟨1, 8, 1, 4, 4, 2, 8036148512681666911947614964378044767940483481600000⟩,
  ⟨1, 8, 2, 4, 5, 2, 449060049309374338594844625170842880291163340800000⟩,
  ⟨1, 8, 3, 4, 6, 2, 1957476514234251087981051299878632177365994700800000⟩,
  ⟨1, 8, 4, 4, 7, 2, 282028763405849995733867128641823358962787942400000⟩,
  ⟨1, 8, 5, 4, 8, 2, -245082536197775526304658178531561776526183628800000⟩,
  ⟨1, 8, 0, 5, 2, 2, 15106245540082893417738201834192172345040515891200000⟩,
  ⟨1, 8, 1, 5, 3, 2, 15346995716626192029912179202901756374144358809600000⟩,
  ⟨1, 8, 2, 5, 4, 2, -2381021152750165303124049375675114536008522137600000⟩,
  ⟨1, 8, 3, 5, 5, 2, 643328525113258592154456668418086283167504793600000⟩,
  ⟨1, 8, 4, 5, 6, 2, -258699003392216757975394843214998822121059123200000⟩,
  ⟨1, 8, 5, 5, 7, 2, 8337325278453891074529792697731013814727475200000⟩,
  ⟨1, 8, 6, 5, 8, 2, -57535457182975545453169818426375693760305561600000⟩,
  ⟨1, 8, 0, 6, 1, 2, -10980191056794126587483095115978659425511538688000000⟩,
  ⟨1, 8, 1, 6, 2, 2, -38243463551890216224091109513902133927255369318400000⟩,
  ⟨1, 8, 2, 6, 3, 2, -1201421021565418637598140706643728138189668352000000⟩,
  ⟨1, 8, 3, 6, 4, 2, -3035230162913957990383182223926250254784423526400000⟩,
  ⟨1, 8, 4, 6, 5, 2, 419760773283985005779011574962663455704324505600000⟩,
  ⟨1, 8, 5, 6, 6, 2, -79302841411040778059384027696653827411070156800000⟩,
  ⟨1, 8, 6, 6, 7, 2, -54336298495781616185074106532288894385677926400000⟩,
  ⟨1, 8, 7, 6, 8, 2, -8515669967151521235499947974662723858543411200000⟩,
  ⟨1, 8, 0, 7, 0, 2, 107092981543187298551581665309130111515122624102400000⟩,
  ⟨1, 8, 1, 7, 1, 2, 109436521925019984069387663440111328929081878118400000⟩,
  ⟨1, 8, 2, 7, 2, 2, 5810785115634651520203951231348216150583620403200000⟩,
  ⟨1, 8, 3, 7, 3, 2, 5409410294334297556601188725606903770650981171200000⟩,
  ⟨1, 8, 4, 7, 4, 2, 1735968262584979330343526802024144076381827891200000⟩,
  ⟨1, 8, 5, 7, 5, 2, 89683611414689255483016725752321391102577868800000⟩,
  ⟨1, 8, 6, 7, 6, 2, 58809254265814184752781655105191709146873856000000⟩,
  ⟨1, 8, 7, 7, 7, 2, 3009715722895977481274365568775599813138841600000⟩,
  ⟨1, 8, 8, 7, 8, 2, 10094747563021883768170106500796598567567360000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0928
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0928. -/
namespace LaughlinFock
def collectedFourData_9_7_5 : List CollectedFourTerm := [
  ⟨2, 5, 2, 1, 8, 0, 3672566024041524166162858408401067156340893286400000⟩,
  ⟨2, 5, 2, 2, 7, 0, 4464162553652484722384663463043768588713118924800000⟩,
  ⟨2, 5, 3, 2, 8, 0, 1877880595030303318713989741838731057936990208000000⟩,
  ⟨2, 5, 2, 3, 6, 0, 1773401462810323179259364544440737384410120192000000⟩,
  ⟨2, 5, 3, 3, 7, 0, 4688860201419518322337002347089844387258459750400000⟩,
  ⟨2, 5, 4, 3, 8, 0, 1361927604175938008493577208170632917536053657600000⟩,
  ⟨2, 5, 2, 4, 5, 0, 823601743810265746259617747930048427478692659200000⟩,
  ⟨2, 5, 3, 4, 6, 0, 10770370731511750900323070049656322939397183897600000⟩,
  ⟨2, 5, 4, 4, 7, 0, 3103541030242281834452108841427905729607080345600000⟩,
  ⟨2, 5, 5, 4, 8, 0, -4494953503442658145715696691904012556238323712000000⟩,
  ⟨2, 5, 2, 5, 4, 0, -4366928602243905291993634641141679028733109862400000⟩,
  ⟨2, 5, 3, 5, 5, 0, 3539703627216690747533978208915896849640141619200000⟩,
  ⟨2, 5, 4, 5, 6, 0, -2846812366989508701795794995907152899369389260800000⟩,
  ⟨2, 5, 5, 5, 7, 0, 152911301029973184292062993173816974925365248000000⟩,
  ⟨2, 5, 6, 5, 8, 0, -1582849652502932910309286407660780448515096576000000⟩,
  ⟨2, 5, 2, 6, 3, 0, -2203474679908323702503505591267101654434971648000000⟩,
  ⟨2, 5, 3, 6, 4, 0, -16700355724491752487719906634892584964651273420800000⟩,
  ⟨2, 5, 4, 6, 5, 0, 4619191202488722711230217672263981290578404966400000⟩,
  ⟨2, 5, 5, 6, 6, 0, -1454459344038527472585494146551032005559058432000000⟩,
  ⟨2, 5, 6, 6, 7, 0, -1494838059925808150013943030486293266357551104000000⟩,
  ⟨2, 5, 7, 6, 8, 0, -327982713123436399665707872354196525369052364800000⟩,
  ⟨2, 5, 2, 7, 2, 0, 10657311336209151474689564375787690724988603596800000⟩,
  ⟨2, 5, 3, 7, 3, 0, 29763501061277280599687103588900792044205008486400000⟩,
  ⟨2, 5, 4, 7, 4, 0, 19103188855875177784517635954432988224047336652800000⟩,
  ⟨2, 5, 5, 7, 5, 0, 1644848586863556205250578649394125294442381312000000⟩,
  ⟨2, 5, 6, 7, 6, 0, 1617892900069704345245123732019873233145692160000000⟩,
  ⟨2, 5, 7, 7, 7, 0, 115919796367576051363230147371233315333236326400000⟩,
  ⟨2, 5, 8, 7, 8, 0, 518401598744846170609932290728320145733713920000000⟩
]

def collectedFourData_9_7_6 : List CollectedFourTerm := [
  ⟨2, 6, 1, 0, 8, 1, 1497656865645179593575374673866991924084001996800000⟩,
  ⟨2, 6, 1, 1, 7, 1, 15705470326546771752898422037695822624862293196800000⟩,
  ⟨2, 6, 2, 1, 8, 1, -8636288876982693765557541923967837022827891916800000⟩,
  ⟨2, 6, 1, 2, 6, 1, 18623767935341427713571005817849817320106701619200000⟩,
  ⟨2, 6, 2, 2, 7, 1, -10497781974447547752119576314021468296485378457600000⟩,
  ⟨2, 6, 3, 2, 8, 1, -2207981992562604201288790894130280815602434048000000⟩,
  ⟨2, 6, 1, 3, 5, 1, 15386105409844248819932813946762650953006134067200000⟩,
  ⟨2, 6, 2, 3, 6, 1, -4170274197232639097580009768819556771329736704000000⟩,
  ⟨2, 6, 3, 3, 7, 1, -5513086890495663763152082135916551823490967142400000⟩,
  ⟨2, 6, 4, 3, 8, 1, -1067555141028859583019330357566229835038484070400000⟩,
  ⟨2, 6, 1, 4, 4, 1, -17329592273482544705800430988440105584028968550400000⟩,
  ⟨2, 6, 2, 4, 5, 1, -1936755536202642291630678361055893284108789350400000⟩,
  ⟨2, 6, 3, 4, 6, 1, -12663629781007199096148938857461474129897691545600000⟩,
  ⟨2, 6, 4, 4, 7, 1, -2432729296381264771212562812402060069114898022400000⟩,
  ⟨2, 6, 5, 4, 8, 1, 2642547246952999962466887702475914975155060736000000⟩,
  ⟨2, 6, 1, 5, 3, 1, -33095104946394889195719844427321454989360391782400000⟩,
  ⟨2, 6, 2, 5, 4, 1, 10269129722175473781263351591655036846938574028800000⟩,
  ⟨2, 6, 3, 5, 5, 1, -4161926955625667022442742154969254317360624435200000⟩,
  ⟨2, 6, 4, 5, 6, 1, 2231490990127242067954721650986263042455712563200000⟩,
  ⟨2, 6, 5, 5, 7, 1, -89895332010726733599941250837646293696774144000000⟩,
  ⟨2, 6, 6, 5, 8, 1, 744435730133108761299691729404737897200248422400000⟩,
  ⟨2, 6, 1, 6, 2, 1, 82470306445206562574769331617471236694951434649600000⟩,
  ⟨2, 6, 2, 6, 3, 1, 5181620628255884296741339280248079651098853376000000⟩,
  ⟨2, 6, 3, 6, 4, 1, 19636011366565378896367246534295107543912729804800000⟩,
  ⟨2, 6, 4, 6, 5, 1, -3620780796638499511854593007138101711607536025600000⟩,
  ⟨2, 6, 5, 6, 6, 1, 855065026245628661816712753983925683692240896000000⟩,
  ⟨2, 6, 6, 6, 7, 1, 703042680529992293358603181308327911898061209600000⟩,
  ⟨2, 6, 7, 6, 8, 1, 128545610827595070482451709667063819633531289600000⟩,
  ⟨2, 6, 1, 7, 1, 1, -235994929884113057626650475333870920035498301849600000⟩,
  ⟨2, 6, 2, 7, 2, 1, -25061392701705179981031343665348723848985024921600000⟩,
  ⟨2, 6, 3, 7, 3, 1, -34995448886811526258847082304289346068286957158400000⟩,
  ⟨2, 6, 4, 7, 4, 1, -14974149441279877407703144838321703885881946931200000⟩,
  ⟨2, 6, 5, 7, 5, 1, -966993340763546356611553906295464884789313536000000⟩,
  ⟨2, 6, 6, 7, 6, 1, -760917046313298807468971509057752495065923584000000⟩,
  ⟨2, 6, 7, 7, 7, 1, -45432214671242477286159833512692750979222732800000⟩,
  ⟨2, 6, 8, 7, 8, 1, -174150947155678117638717317700929490486558720000000⟩
]

def collectedFourData_9_7_7 : List CollectedFourTerm := [
  ⟨2, 7, 0, 0, 7, 2, -7336567906022294078368560924608599661039163801600000⟩,
  ⟨2, 7, 1, 0, 8, 2, -844194112741415445229062317587529416269260390400000⟩,
  ⟨2, 7, 0, 1, 6, 2, -923024929257193213578961284398079076465429708800000⟩,
  ⟨2, 7, 1, 1, 7, 2, -8852805934151098453714227467293191628453733990400000⟩,
  ⟨2, 7, 2, 1, 8, 2, 2434036925655256304906091537741930713826145075200000⟩,
  ⟨2, 7, 0, 2, 5, 2, 4464162553652484722384663463043768588713118924800000⟩,
  ⟨2, 7, 1, 2, 6, 2, -10497781974447547752119576314021468296485378457600000⟩,
  ⟨2, 7, 2, 2, 7, 2, 2958676964984838485717271786498351355350378086400000⟩,
  ⟨2, 7, 3, 2, 8, 2, 414862585664758303845868364859383900220162048000000⟩,
  ⟨2, 7, 0, 3, 4, 2, -2835000605796283615776938974077008226291390873600000⟩,
  ⟨2, 7, 1, 3, 5, 2, -8672787407423830978095141424656184425664059801600000⟩,
  ⟨2, 7, 2, 3, 6, 2, 1175342966262372698601050850123999520600621056000000⟩,
  ⟨2, 7, 3, 3, 7, 2, 1035866003477228869004458968249488173917693542400000⟩,
  ⟨2, 7, 4, 3, 8, 2, 150438959977516973493690488944340454439963852800000⟩,
  ⟨2, 7, 0, 4, 3, 2, -10880016822416172929840420287238566982576190259200000⟩,
  ⟨2, 7, 1, 4, 4, 2, 9768285452476316668397043238995862874815148851200000⟩,
  ⟨2, 7, 2, 4, 5, 2, 545851876683805320689366587144435742650505625600000⟩,
  ⟨2, 7, 3, 4, 6, 2, 2379397210913133528399638877224766610735733145600000⟩,
  ⟨2, 7, 4, 4, 7, 2, 342818137620247317894239318693069289429978316800000⟩,
  ⟨2, 7, 5, 4, 8, 2, -297908403412251008445547320331330479531334041600000⟩,
  ⟨2, 7, 0, 5, 2, 2, 18362293618374831648094564740373416800229418598400000⟩,
  ⟨2, 7, 1, 5, 3, 2, 18654935851591131406290963338224742644902474547200000⟩,
  ⟨2, 7, 2, 5, 4, 2, -2894234004230274985222328337340995732298216243200000⟩,
  ⟨2, 7, 3, 5, 5, 2, 781993595950834699819008879510303895501091635200000⟩,
  ⟨2, 7, 4, 5, 6, 2, -314459807135027149273481963093711418810590822400000⟩,
  ⟨2, 7, 5, 5, 7, 2, 10134378813627371838907215766279593925174886400000⟩,
  ⟨2, 7, 6, 5, 8, 2, -69936832117415253116862991774996597436527411200000⟩,
  ⟨2, 7, 0, 6, 1, 2, -13346896264576460700099828837058912138051977216000000⟩,
  ⟨2, 7, 1, 6, 2, 2, -46486580987983249615788385873920630844071660748800000⟩,
  ⟨2, 7, 2, 6, 3, 2, -1460379119267976748631995805965446949386584064000000⟩,
  ⟨2, 7, 3, 6, 4, 2, -3689453299490585403304938286918581927484902604800000⟩,
  ⟨2, 7, 4, 6, 5, 2, 510237341771309979551811491554297599575143219200000⟩,
  ⟨2, 7, 5, 6, 6, 2, -96396027384641254300435914834017861729098137600000⟩,
  ⟨2, 7, 6, 6, 7, 2, -66048116619566464493710104311184529550003404800000⟩,
  ⟨2, 7, 7, 6, 8, 2, -10351164482207572221716216884219753747867238400000⟩,
  ⟨2, 7, 0, 7, 0, 2, 130176142466727772848482390943490868708771679436800000⟩,
  ⟨2, 7, 1, 7, 1, 2, 133024816975794034270116109421168957693769862348800000⟩,
  ⟨2, 7, 2, 7, 2, 2, 7063260170334827088665112924559066225392903782400000⟩,
  ⟨2, 7, 3, 7, 3, 2, 6575371746954984072166201618918304788018259558400000⟩,
  ⟨2, 7, 4, 7, 4, 2, 2110144368114811730151407749415528312412202598400000⟩,
  ⟨2, 7, 5, 7, 5, 2, 109014301481009831066899658002294859892365721600000⟩,
  ⟨2, 7, 6, 7, 6, 2, 71485187463768512162884855630771684525473792000000⟩,
  ⟨2, 7, 7, 7, 7, 2, 3658439396143427173622573658716746632344371200000⟩,
  ⟨2, 7, 8, 7, 8, 2, 12270601471672124553793232613663357555179520000000⟩
]

def collectedFourData_9_7_8 : List CollectedFourTerm := [
  ⟨2, 8, 0, 0, 7, 3, -3086177606496240931993294916182592967552270336000000⟩,
  ⟨2, 8, 1, 0, 8, 3, -177558021656141562073273273167624922560724992000000⟩,
  ⟨2, 8, 0, 1, 6, 3, -388276766929807844763588765766514652739534848000000⟩,
  ⟨2, 8, 1, 1, 7, 3, -1861996765967856110240166057166861758986452992000000⟩,
  ⟨2, 8, 2, 1, 8, 3, 341298108759910970489581992457920204729483264000000⟩,
  ⟨2, 8, 0, 2, 5, 3, 1877880595030303318713989741838731057936990208000000⟩,
  ⟨2, 8, 1, 2, 6, 3, -2207981992562604201288790894130280815602434048000000⟩,
  ⟨2, 8, 2, 2, 7, 3, 414862585664758303845868364859383900220162048000000⟩,
  ⟨2, 8, 3, 2, 8, 3, 43628697984268846568595100667729216557547520000000⟩,
  ⟨2, 8, 0, 3, 4, 3, -1192562448284545402417480504130020321794195456000000⟩,
  ⟨2, 8, 1, 3, 5, 3, -1824133752017961807148682091057152733550215168000000⟩,
  ⟨2, 8, 2, 3, 6, 3, 164805359894703280485613307766851973855313920000000⟩,
  ⟨2, 8, 3, 3, 7, 3, 108936034676309668967815686009753586920062976000000⟩,
  ⟨2, 8, 4, 3, 8, 3, 12656636055834423475665776874917064708037017600000⟩,
  ⟨2, 8, 0, 4, 3, 3, -4576753695427616054399262433077570687763218432000000⟩,
  ⟨2, 8, 1, 4, 4, 3, 2054548135003918023437794552427599240548581376000000⟩,
  ⟨2, 8, 2, 4, 5, 3, 76538778525341550579567806482422443689377792000000⟩,
  ⟨2, 8, 3, 4, 6, 3, 250227438883648609809199693235319360291078144000000⟩,
  ⟨2, 8, 4, 4, 7, 3, 28841760152070179570366922937650323113220505600000⟩,
  ⟨2, 8, 5, 4, 8, 3, -20886202176434576035500922074238307014803456000000⟩,
  ⟨2, 8, 0, 5, 2, 3, 7724224745799692564484952837026863660258033664000000⟩,
  ⟨2, 8, 1, 5, 3, 3, 3923663354124039579969082923026360255649939456000000⟩,
  ⟨2, 8, 2, 5, 4, 3, -405826461193269149916478339200362274329985024000000⟩,
  ⟨2, 8, 3, 5, 5, 3, 82237742332688561492846960834239985350606848000000⟩,
  ⟨2, 8, 4, 5, 6, 3, -26455934910017544670320385566158281801256140800000⟩,
  ⟨2, 8, 5, 5, 7, 3, 710515992196049387779524106179825603969024000000⟩,
  ⟨2, 8, 6, 5, 8, 3, -4202772583171674444670460887927476071694336000000⟩,
  ⟨2, 8, 0, 6, 1, 3, -5614463451521010298511205880356141241057935360000000⟩,
  ⟨2, 8, 1, 6, 2, 3, -9777449557164355502161739671344373066182426624000000⟩,
  ⟨2, 8, 2, 6, 3, 3, -204772830775542254628121048860776127245844480000000⟩,
  ⟨2, 8, 3, 6, 4, 3, -387998458507926790503821782728810212729290752000000⟩,
  ⟨2, 8, 4, 6, 5, 3, 42926967441552385198195740445742248101308006400000⟩,
  ⟨2, 8, 5, 6, 6, 3, -6758275006343595723449615571457324735266816000000⟩,
  ⟨2, 8, 6, 6, 7, 3, -3969084748259804815056482729961041789190144000000⟩,
  ⟨2, 8, 7, 6, 8, 3, -544286041432354587594373643860744505131008000000⟩,
  ⟨2, 8, 0, 7, 0, 3, 54759487123550215883037923823222380843633737728000000⟩,
  ⟨2, 8, 1, 7, 1, 3, 27978900796512918159929528022892489572429594624000000⟩,
  ⟨2, 8, 2, 7, 2, 3, 990402944345437704914108899690984101818400768000000⟩,
  ⟨2, 8, 3, 7, 3, 3, 691493805406715548131154088167684661959458816000000⟩,
  ⟨2, 8, 4, 7, 4, 3, 177529340115680601492051307847219655184534732800000⟩,
  ⟨2, 8, 5, 7, 5, 3, 7642935596228732937847765113851364828512256000000⟩,
  ⟨2, 8, 6, 7, 6, 3, 4295819196832065402913370624221765183733760000000⟩,
  ⟨2, 8, 7, 7, 7, 3, 192368452860524195630599458156522183327744000000⟩,
  ⟨2, 8, 8, 7, 8, 3, 573523629474227122595575033320260291788800000000⟩
]

def collectedFourData_9_7_9 : List CollectedFourTerm := [
  ⟨3, 4, 2, 1, 8, 0, -2332291169474980664478070748590701384087424204800000⟩,
  ⟨3, 4, 2, 2, 7, 0, -2835000605796283615776938974077008226291390873600000⟩,
  ⟨3, 4, 3, 2, 8, 0, -1192562448284545402417480504130020321794195456000000⟩,
  ⟨3, 4, 2, 3, 6, 0, -1126212175511800970879989707509226487198777344000000⟩,
  ⟨3, 4, 3, 3, 7, 0, -2977696567218957481292523226110626075710901452800000⟩,
  ⟨3, 4, 4, 3, 8, 0, -864902551483126899569951887311398207711556403200000⟩,
  ⟨3, 4, 2, 4, 5, 0, -523034592619527958621648141703656467316762214400000⟩,
  ⟨3, 4, 3, 4, 6, 0, -6839806387315374029700833506611470159989388083200000⟩,
  ⟨3, 4, 4, 4, 7, 0, -1970927490902343737702136452892954840351847219200000⟩,
  ⟨3, 4, 5, 4, 8, 0, 2854554634185497135136319699070780964008361984000000⟩,
  ⟨3, 4, 2, 5, 4, 0, 2773251440564441597138142834086514049864748236800000⟩,
  ⟨3, 4, 3, 5, 5, 0, -2247915887222373276512993139761082492470584934400000⟩,
  ⟨3, 4, 4, 5, 6, 0, 1807889987876968925066568666451878054939171225600000⟩,
  ⟨3, 4, 5, 5, 7, 0, -97107492355624064813920297420317450081140736000000⟩,
  ⟨3, 4, 6, 5, 8, 0, 1005200789576708241206319153648076177677484032000000⟩,
  ⟨3, 4, 2, 6, 3, 0, 1399333464523110997790917626361394982379585536000000⟩,
  ⟨3, 4, 3, 6, 4, 0, 10605688755041062542200951430378504309257640345600000⟩,
  ⟨3, 4, 4, 6, 5, 0, -2933452736085965633645256609812250915299445964800000⟩,
  ⟨3, 4, 5, 6, 6, 0, 923665541274167177327244481985763170555265024000000⟩,
  ⟨3, 4, 6, 6, 7, 0, 949308353924001525487152743616035550268489728000000⟩,
  ⟨3, 4, 7, 6, 8, 0, 208287932892336637854556270101256289998444953600000⟩,
  ⟨3, 4, 2, 7, 2, 0, -6768007152784457303420411098553548476679559577600000⟩,
  ⟨3, 4, 3, 7, 3, 0, -18901539208132516955249222974395674131897830604800000⟩,
  ⟨3, 4, 4, 7, 4, 0, -12131626330393449335570112411484807636870338969600000⟩,
  ⟨3, 4, 5, 7, 5, 0, -1044573687485025257323152128478275973817565184000000⟩,
  ⟨3, 4, 6, 7, 6, 0, -1027455272223085444014578180724194773429125120000000⟩,
  ⟨3, 4, 7, 7, 7, 0, -73615754125480830737183613776731143746145484800000⟩,
  ⟨3, 4, 8, 7, 8, 0, -329214903987971590906066623460346753911357440000000⟩
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0929
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0929. -/
namespace LaughlinFock

def collectedFourData_9_7_24 : List CollectedFourTerm := [
  ⟨5, 6, 0, 0, 7, 4, 4678555495035510740948935086498247056811465113600000⟩,
  ⟨5, 6, 1, 0, 8, 4, 179448531231290552211480564899074214894292172800000⟩,
  ⟨5, 6, 0, 1, 6, 4, 588616286272793100104325854320634995948702924800000⟩,
  ⟨5, 6, 1, 1, 7, 4, 1881821962723966326777047953476592206466567372800000⟩,
  ⟨5, 6, 2, 1, 8, 4, -258699003392216757975394843214998822121059123200000⟩,
  ⟨5, 6, 0, 2, 5, 4, -2846812366989508701795794995907152899369389260800000⟩,
  ⟨5, 6, 1, 2, 6, 4, 2231490990127242067954721650986263042455712563200000⟩,
  ⟨5, 6, 2, 2, 7, 4, -314459807135027149273481963093711418810590822400000⟩,
  ⟨5, 6, 3, 2, 8, 4, -26455934910017544670320385566158281801256140800000⟩,
  ⟨5, 6, 0, 3, 4, 4, 1807889987876968925066568666451878054939171225600000⟩,
  ⟨5, 6, 1, 3, 5, 4, 1843555810747703959178010911911739441630360371200000⟩,
  ⟨5, 6, 2, 3, 6, 4, -124920066253420950159695007448240070376554496000000⟩,
  ⟨5, 6, 3, 3, 7, 4, -66057544137370868371028788066577736283497431040000⟩,
  ⟨5, 6, 4, 3, 8, 4, -6395697387716198597938015402847617622653009920000⟩,
  ⟨5, 6, 0, 4, 3, 4, 6938225494895228623779616491544000115101610803200000⟩,
  ⟨5, 6, 1, 4, 4, 4, -2076423479669288473116238422723904144406898278400000⟩,
  ⟨5, 6, 2, 4, 5, 4, -58015281119803372490534858022034110624143769600000⟩,
  ⟨5, 6, 3, 4, 6, 4, -151735007957220440853746785868316400064145653760000⟩,
  ⟨5, 6, 4, 4, 7, 4, -14574423191753154779823296697090389789135339520000⟩,
  ⟨5, 6, 5, 4, 8, 4, 9046535731013847472110156717556210075277721600000⟩,
  ⟨5, 6, 0, 5, 2, 4, -11709700068227243265675529798720590702870685286400000⟩,
  ⟨5, 6, 1, 5, 3, 4, -3965439687693456367640359687105411991806043750400000⟩,
  ⟨5, 6, 2, 5, 4, 4, 307610556186066586749751170312576150610850611200000⟩,
  ⟨5, 6, 3, 5, 5, 4, -49868010250612665608418376170039465199188049920000⟩,
  ⟨5, 6, 4, 5, 6, 4, 13368809298706957702852095707950939182056079360000⟩,
  ⟨5, 6, 5, 5, 7, 4, -307749022850623987165515592973335371605606400000⟩,
  ⟨5, 6, 6, 5, 8, 4, 1592820251335588165259508417958525899531878400000⟩,
  ⟨5, 6, 0, 6, 1, 4, 8511363305046927924022853771067588925861134336000000⟩,
  ⟨5, 6, 1, 6, 2, 4, 9881552778387174928023538225716364560251328921600000⟩,
  ⟨5, 6, 2, 6, 3, 4, 155214827986935055892454703863204485397479424000000⟩,
  ⟨5, 6, 3, 6, 4, 4, 235277751519746122192478401319708989396699054080000⟩,
  ⟨5, 6, 4, 6, 5, 4, -21692011393655782542750277268878145287492730880000⟩,
  ⟨5, 6, 5, 6, 6, 4, 2927242387507235916174811691806261717342617600000⟩,
  ⟨5, 6, 6, 6, 7, 4, 1504254261010817575387964910323756657383833600000⟩,
  ⟨5, 6, 7, 6, 8, 4, 183360402032186507762185744109059873072742400000⟩,
  ⟨5, 6, 0, 7, 0, 4, -83013789889452433518411984705537802816562449612800000⟩,
  ⟨5, 6, 1, 7, 1, 4, -28276799924722324027127793571509846532320500121600000⟩,
  ⟨5, 6, 2, 7, 2, 4, -750711029691404871925959470614686927713363558400000⟩,
  ⟨5, 6, 3, 7, 3, 4, -419313799213460240331249041916014556669951344640000⟩,
  ⟨5, 6, 4, 7, 4, 4, -89709772155250854709833324776301027806423285760000⟩,
  ⟨5, 6, 5, 7, 5, 4, -3310419451896922389886685485675120879573401600000⟩,
  ⟨5, 6, 6, 7, 6, 4, -1628084241385847654001338340483008292716544000000⟩,
  ⟨5, 6, 7, 7, 7, 4, -64805551070152206670291049605405399528243200000⟩,
  ⟨5, 6, 8, 7, 8, 4, -173889028457806860685604058022658049048576000000⟩
]

def collectedFourData_9_7_25 : List CollectedFourTerm := [
  ⟨5, 7, 0, 0, 7, 5, -251300021027851133446563808814051038662230016000000⟩,
  ⟨5, 7, 1, 0, 8, 5, -7229061360877055950830256298918772763262976000000⟩,
  ⟨5, 7, 0, 1, 6, 5, -31616443424610019548458635209709582798553088000000⟩,
  ⟨5, 7, 1, 1, 7, 5, -75808959512985661394569965766880503032446976000000⟩,
  ⟨5, 7, 2, 1, 8, 5, 8337325278453891074529792697731013814727475200000⟩,
  ⟨5, 7, 0, 2, 5, 5, 152911301029973184292062993173816974925365248000000⟩,
  ⟨5, 7, 1, 2, 6, 5, -89895332010726733599941250837646293696774144000000⟩,
  ⟨5, 7, 2, 2, 7, 5, 10134378813627371838907215766279593925174886400000⟩,
  ⟨5, 7, 3, 2, 8, 5, 710515992196049387779524106179825603969024000000⟩,
  ⟨5, 7, 0, 3, 4, 5, -97107492355624064813920297420317450081140736000000⟩,
  ⟨5, 7, 1, 3, 5, 5, -74267412425456133510032608017435434107797504000000⟩,
  ⟨5, 7, 2, 3, 6, 5, 4025911242424662492583345780226877403693056000000⟩,
  ⟨5, 7, 3, 3, 7, 5, 1774079868068713140498352371675177294181171200000⟩,
  ⟨5, 7, 4, 3, 8, 5, 147228491149793064302171555323771712490700800000⟩,
  ⟨5, 7, 0, 4, 3, 5, -372674047494633780877557783354129493725806592000000⟩,
  ⟨5, 7, 1, 4, 4, 5, 83648456984850105244502423459464961618608128000000⟩,
  ⟨5, 7, 2, 4, 5, 5, 1869710603729746847128367716344930821052825600000⟩,
  ⟨5, 7, 3, 4, 6, 5, 4075083723039309311264207993951547202260172800000⟩,
  ⟨5, 7, 4, 4, 7, 5, 335502167444884138500121102386887649971404800000⟩,
  ⟨5, 7, 5, 4, 8, 5, -182219273276120281262242160910642431655936000000⟩,
  ⟨5, 7, 0, 5, 2, 5, 628965046262211979988932700376684645511593984000000⟩,
  ⟨5, 7, 1, 5, 3, 5, 159747235758899129996063011538851905423802368000000⟩,
  ⟨5, 7, 2, 5, 4, 5, -9913641847785000724244946056668532392014643200000⟩,
  ⟨5, 7, 3, 5, 5, 5, 1339284319475721082732844091945025376197017600000⟩,
  ⟨5, 7, 4, 5, 6, 5, -307749022850623987165515592973335371605606400000⟩,
  ⟨5, 7, 5, 5, 7, 5, 6198815210890919031800067945922710994944000000⟩,
  ⟨5, 7, 6, 5, 8, 5, -28518472071059780324459467609227204231168000000⟩,
  ⟨5, 7, 0, 6, 1, 5, -457172257506317980077338215229460756729692160000000⟩,
  ⟨5, 7, 1, 6, 2, 5, -398077102585111555913527186760712861486415872000000⟩,
  ⟨5, 7, 2, 6, 3, 5, -5002247755103952693617003064905331652952064000000⟩,
  ⟨5, 7, 3, 6, 4, 5, -6318756287815387668166388248529707490240102400000⟩,
  ⟨5, 7, 4, 6, 5, 5, 499348532909946443589307421361907277443891200000⟩,
  ⟨5, 7, 5, 6, 6, 5, -58961794482941321004267975642369119748096000000⟩,
  ⟨5, 7, 6, 6, 7, 5, -26932752201284862471121485058108211331072000000⟩,
  ⟨5, 7, 7, 6, 8, 5, -2954660232325445560758098427134935774003200000⟩,
  ⟨5, 7, 0, 7, 0, 5, 4458933353886117008548119971549369655380410368000000⟩,
  ⟨5, 7, 1, 7, 1, 5, 1139127304873797008763963052485555485379919872000000⟩,
  ⟨5, 7, 2, 7, 2, 5, 24193839027555395362703800888708613802452582400000⟩,
  ⟨5, 7, 3, 7, 3, 5, 11261335541645735006662653728979569647760179200000⟩,
  ⟨5, 7, 4, 7, 4, 5, 2065112464698022474241339654958935926269542400000⟩,
  ⟨5, 7, 5, 7, 5, 5, 66679914245603311896489152553741226868736000000⟩,
  ⟨5, 7, 6, 7, 6, 5, 29149852237477925329023480495929693306880000000⟩,
  ⟨5, 7, 7, 7, 7, 5, 1044273367961436588038690830158898239897600000⟩,
  ⟨5, 7, 8, 7, 8, 5, 2547308180192589354532291462063592570880000000⟩
]

def collectedFourData_9_7_26 : List CollectedFourTerm := [
  ⟨5, 8, 0, 0, 7, 6, 2601312972152033855917386303257822851227451392000000⟩,
  ⟨5, 8, 1, 0, 8, 6, 59864861189003691227716582784993799762975129600000⟩,
  ⟨5, 8, 0, 1, 6, 6, 327275199092139878703593340416527867268038656000000⟩,
  ⟨5, 8, 1, 1, 7, 6, 627784522993326112635925428344323598146181529600000⟩,
  ⟨5, 8, 2, 1, 8, 6, -57535457182975545453169818426375693760305561600000⟩,
  ⟨5, 8, 0, 2, 5, 6, -1582849652502932910309286407660780448515096576000000⟩,
  ⟨5, 8, 1, 2, 6, 6, 744435730133108761299691729404737897200248422400000⟩,
  ⟨5, 8, 2, 2, 7, 6, -69936832117415253116862991774996597436527411200000⟩,
  ⟨5, 8, 3, 2, 8, 6, -4202772583171674444670460887927476071694336000000⟩,
  ⟨5, 8, 0, 3, 4, 6, 1005200789576708241206319153648076177677484032000000⟩,
  ⟨5, 8, 1, 3, 5, 6, 615018757452767494481711990046620696705394278400000⟩,
  ⟨5, 8, 2, 3, 6, 6, -27782608471519176356389337139885591125557248000000⟩,
  ⟨5, 8, 3, 3, 7, 6, -10493858423694275418532421393858303347182796800000⟩,
  ⟨5, 8, 4, 3, 8, 6, -762012240054452282206390436016610947681484800000⟩,
  ⟨5, 8, 0, 4, 3, 6, 3857706935984508001116743308547691964482453504000000⟩,
  ⟨5, 8, 1, 4, 4, 6, -692704490402175421078869115435801765477141708800000⟩,
  ⟨5, 8, 2, 4, 5, 6, -12902777664612997636513162850429952563399884800000⟩,
  ⟨5, 8, 3, 4, 6, 6, -24104524505330324877176990759531440378164019200000⟩,
  ⟨5, 8, 4, 4, 7, 6, -1736462529509251400806799301604612923772108800000⟩,
  ⟨5, 8, 5, 4, 8, 6, 838323950454875275660793080427566640136192000000⟩,
  ⟨5, 8, 0, 5, 2, 6, -6510683632974173923722807058976129284055236608000000⟩,
  ⟨5, 8, 1, 5, 3, 6, -1322889046949975735325037620140140397647940812800000⟩,
  ⟨5, 8, 2, 5, 4, 6, 68413537556779032133447248507421752857041305600000⟩,
  ⟨5, 8, 3, 5, 5, 6, -7921999618287537738223951151714085179385446400000⟩,
  ⟨5, 8, 4, 5, 6, 6, 1592820251335588165259508417958525899531878400000⟩,
  ⟨5, 8, 5, 5, 7, 6, -28518472071059780324459467609227204231168000000⟩,
  ⟨5, 8, 6, 5, 8, 6, 118082714105593237572557131321588859692646400000⟩,
  ⟨5, 8, 0, 6, 1, 6, 4732383702536231561395209456154853720897617920000000⟩,
  ⟨5, 8, 1, 6, 2, 6, 3296531776275757456649092277900358578760528691200000⟩,
  ⟨5, 8, 2, 6, 3, 6, 34520257027298218801786591519337327427059712000000⟩,
  ⟨5, 8, 3, 6, 4, 6, 37376070317705926498856338301341328855374233600000⟩,
  ⟨5, 8, 4, 6, 5, 6, -2584484097873929050404462382491964043113267200000⟩,
  ⟨5, 8, 5, 6, 6, 6, 271261560800689946213744071873416986099712000000⟩,
  ⟨5, 8, 6, 6, 7, 6, 111516930862801441108459474958918914513305600000⟩,
  ⟨5, 8, 7, 6, 8, 6, 11121796255854089119433303884811801827737600000⟩,
  ⟨5, 8, 0, 7, 0, 6, -46156308017737197571158609637330730494004822016000000⟩,
  ⟨5, 8, 1, 7, 1, 6, -9433271427454067014594120855735824516436407091200000⟩,
  ⟨5, 8, 2, 7, 2, 6, -166960451100434359126851018151054443428393779200000⟩,
  ⟨5, 8, 3, 7, 3, 6, -66611916950725308619421866395875359534664908800000⟩,
  ⟨5, 8, 4, 7, 4, 6, -10688426967494076182929512492765480080533094400000⟩,
  ⟨5, 8, 5, 7, 5, 6, -306769795100988690859326569756052833697792000000⟩,
  ⟨5, 8, 6, 7, 6, 6, -120696987531509114185511661888181238759424000000⟩,
  ⟨5, 8, 7, 7, 7, 6, -3930805818827016197718658312499454856396800000⟩,
  ⟨5, 8, 8, 7, 8, 6, -8789422017158774444225469129028030955520000000⟩
]

def collectedFourData_9_7_28 : List CollectedFourTerm := [
  ⟨6, 2, 1, 0, 8, 1, 6631967338099306923778284383041111674929440358400000⟩,
  ⟨6, 2, 1, 1, 7, 1, 69547416784468498693099004509807211260336825958400000⟩,
  ⟨6, 2, 2, 1, 8, 1, -38243463551890216224091109513902133927255369318400000⟩,
  ⟨6, 2, 1, 2, 6, 1, 82470306445206562574769331617471236694951434649600000⟩,
  ⟨6, 2, 2, 2, 7, 1, -46486580987983249615788385873920630844071660748800000⟩,
  ⟨6, 2, 3, 2, 8, 1, -9777449557164355502161739671344373066182426624000000⟩,
  ⟨6, 2, 1, 3, 5, 1, 68133195847021981922772723621332846472702040473600000⟩,
  ⟨6, 2, 2, 3, 6, 1, -18466928507719746709360839410785226725263409152000000⟩,
  ⟨6, 2, 3, 3, 7, 1, -24413210414603085490018813796264003410865632051200000⟩,
  ⟨6, 2, 4, 3, 8, 1, -4727378473221493205629414128290272649701176115200000⟩,
  ⟨6, 2, 1, 4, 4, 1, -76739400443908527278967818866363608584437314355200000⟩,
  ⟨6, 2, 2, 4, 5, 1, -8576396738545058717229801417572893724681384755200000⟩,
  ⟨6, 2, 3, 4, 6, 1, -56077450727167331748614433184199006391246834892800000⟩,
  ⟨6, 2, 4, 4, 7, 1, -10772682051631060224754908756650044378527773491200000⟩,
  ⟨6, 2, 5, 4, 8, 1, 11701803953355346113613806411994672274570477568000000⟩,
  ⟨6, 2, 1, 5, 3, 1, -146552698478704538651865380965018561737477272371200000⟩,
  ⟨6, 2, 2, 5, 4, 1, 45474056488121942953450257565777492844000732774400000⟩,
  ⟨6, 2, 3, 5, 5, 1, -18429965011627593263458795172298227591767759257600000⟩,
  ⟨6, 2, 4, 5, 6, 1, 9881552778387174928023538225716364560251328921600000⟩,
  ⟨6, 2, 5, 5, 7, 1, -398077102585111555913527186760712861486415872000000⟩,
  ⟨6, 2, 6, 5, 8, 1, 3296531776275757456649092277900358578760528691200000⟩,
  ⟨6, 2, 1, 6, 2, 1, 365197390172569855197721225257183700984093527244800000⟩,
  ⟨6, 2, 2, 6, 3, 1, 22945401949738821023410961971711844561492901888000000⟩,
  ⟨6, 2, 3, 6, 4, 1, 86952752009391810029002436559789321078211765862400000⟩,
  ⟨6, 2, 4, 6, 5, 1, -16033645978966708346973108976484198194214653132800000⟩,
  ⟨6, 2, 5, 6, 6, 1, 3786423616847049058604194225370660515923099648000000⟩,
  ⟨6, 2, 6, 6, 7, 1, 3113233879882158090669711402328413419460152524800000⟩,
  ⟨6, 2, 7, 6, 8, 1, 569229382257316961726062186627224374245903564800000⟩,
  ⟨6, 2, 1, 7, 1, 1, -1045039556690601259546517747795752977575900400844800000⟩,
  ⟨6, 2, 2, 7, 2, 1, -110977582153565348898929645100816602928429976780800000⟩,
  ⟨6, 2, 3, 7, 3, 1, -154967856338358047666788965973177219812026430259200000⟩,
  ⟨6, 2, 4, 7, 4, 1, -66308960542577250756618165852978940796401719705600000⟩,
  ⟨6, 2, 5, 7, 5, 1, -4282067808196285191085986991104095880078163968000000⟩,
  ⟨6, 2, 6, 7, 6, 1, -3369514816051574762902744874136421691232878592000000⟩,
  ⟨6, 2, 7, 7, 7, 1, -201184243673464069590092610142994871401997926400000⟩,
  ⟨6, 2, 8, 7, 8, 1, -771180248245959806767697083710708605371023360000000⟩
]

def collectedFourData_9_7_29 : List CollectedFourTerm := [
  ⟨6, 3, 0, 0, 7, 2, 3621270826063786312491702919691299435698978816000000⟩,
  ⟨6, 3, 1, 0, 8, 2, 416687414491982894945606569453500489850159104000000⟩,
  ⟨6, 3, 0, 1, 6, 2, 455597670581760830958964107452455176779071488000000⟩,
  ⟨6, 3, 1, 1, 7, 2, 4369673704216692069152145100076300714171695104000000⟩,
  ⟨6, 3, 2, 1, 8, 2, -1201421021565418637598140706643728138189668352000000⟩,
  ⟨6, 3, 0, 2, 5, 2, -2203474679908323702503505591267101654434971648000000⟩,
  ⟨6, 3, 1, 2, 6, 2, 5181620628255884296741339280248079651098853376000000⟩,
  ⟨6, 3, 2, 2, 7, 2, -1460379119267976748631995805965446949386584064000000⟩,
  ⟨6, 3, 3, 2, 8, 2, -204772830775542254628121048860776127245844480000000⟩,
  ⟨6, 3, 0, 3, 4, 2, 1399333464523110997790917626361394982379585536000000⟩,
  ⟨6, 3, 1, 3, 5, 2, 4280818009382419144161098773410582040795938816000000⟩,
  ⟨6, 3, 2, 3, 6, 2, -580139821353173968164705297625251825907138560000000⟩,
  ⟨6, 3, 3, 3, 7, 2, -511295115938913068906575496176786699267866624000000⟩,
  ⟨6, 3, 4, 3, 8, 2, -74255458935065750282687772048050751881084928000000⟩,
  ⟨6, 3, 0, 4, 3, 2, 5370288670504562270164811569530321466338312192000000⟩,
  ⟨6, 3, 1, 4, 4, 2, -4821547020736903947147290109051060023419994112000000⟩,
  ⟨6, 3, 2, 4, 5, 2, -269428089769966761063915083532353251684909056000000⟩,
  ⟨6, 3, 3, 4, 6, 2, -1174451298464010827269950908955065108718944256000000⟩,
  ⟨6, 3, 4, 4, 7, 2, -169212271502411328244227164356691797966061568000000⟩,
  ⟨6, 3, 5, 4, 8, 2, 147045188422569705774421776794562565521801216000000⟩,
  ⟨6, 3, 0, 5, 2, 2, -9063480231029426587052151848721972191438045184000000⟩,
  ⟨6, 3, 1, 5, 3, 2, -9207926080259615766995513521703265403322499072000000⟩,
  ⟨6, 3, 2, 5, 4, 2, 1428570592895023255007015059333399224917164032000000⟩,
  ⟨6, 3, 3, 5, 5, 2, -385985740397897806949746919254735690716413952000000⟩,
  ⟨6, 3, 4, 5, 6, 2, 155214827986935055892454703863204485397479424000000⟩,
  ⟨6, 3, 5, 5, 7, 2, -5002247755103952693617003064905331652952064000000⟩,
  ⟨6, 3, 6, 5, 8, 2, 34520257027298218801786591519337327427059712000000⟩,
  ⟨6, 3, 0, 6, 1, 2, 6587920493686982587272130378292704217042780160000000⟩,
  ⟨6, 3, 1, 6, 2, 2, 22945401949738821023410961971711844561492901888000000⟩,
  ⟨6, 3, 2, 6, 3, 2, 720831370654498049384984225698400524975472640000000⟩,
  ⟨6, 3, 3, 6, 4, 2, 1821084431945750575418023407312490732556648448000000⟩,
  ⟨6, 3, 4, 6, 5, 2, -251849042194249051498803985328717855868321792000000⟩,
  ⟨6, 3, 5, 6, 6, 2, 47580302695747507036409655374996812307890176000000⟩,
  ⟨6, 3, 6, 6, 7, 2, 32600818379199220519747517494013528478056448000000⟩,
  ⟨6, 3, 7, 6, 8, 2, 5109251415016076581742880019404731222851584000000⟩,
  ⟨6, 3, 0, 7, 0, 2, -64253895418500599130495660303672281606041632768000000⟩,
  ⟨6, 3, 1, 7, 1, 2, -65659978211541386955992164687685860593015717888000000⟩,
  ⟨6, 3, 2, 7, 2, 2, -3486368329084217153516304201227000986441089024000000⟩,
  ⟨6, 3, 3, 7, 3, 2, -3245550532998746882299862536518897303010934784000000⟩,
  ⟨6, 3, 4, 7, 4, 2, -1041550263954409619518576688083176870257885184000000⟩,
  ⟨6, 3, 5, 7, 5, 2, -53808581155890619495466044586450297359958016000000⟩,
  ⟨6, 3, 6, 7, 6, 2, -35284512755037939388005670936280374884433920000000⟩,
  ⟨6, 3, 7, 7, 7, 2, -1805776219054919762028810734216474957709312000000⟩,
  ⟨6, 3, 8, 7, 8, 2, -6056670052920327815638241424015323509555200000000⟩
]

def collectedFourData_9_7_30 : List CollectedFourTerm := [
  ⟨6, 4, 0, 0, 7, 3, 27445974996411339039852459194825464997440231833600000⟩,
  ⟨6, 4, 1, 0, 8, 3, 1579057865149686794134671853720129060165858099200000⟩,
  ⟨6, 4, 0, 1, 6, 3, 3453020465967767472922381322860796153927879884800000⟩,
  ⟨6, 4, 1, 1, 7, 3, 16559097757232333568841911442706685273318830899200000⟩,
  ⟨6, 4, 2, 1, 8, 3, -3035230162913957990383182223926250254784423526400000⟩,
  ⟨6, 4, 0, 2, 5, 3, -16700355724491752487719906634892584964651273420800000⟩,
  ⟨6, 4, 1, 2, 6, 3, 19636011366565378896367246534295107543912729804800000⟩,
  ⟨6, 4, 2, 2, 7, 3, -3689453299490585403304938286918581927484902604800000⟩,
  ⟨6, 4, 3, 2, 8, 3, -387998458507926790503821782728810212729290752000000⟩,
  ⟨6, 4, 0, 3, 4, 3, 10605688755041062542200951430378504309257640345600000⟩,
  ⟨6, 4, 1, 3, 5, 3, 16222374643186616206664262063495967269041523916800000⟩,
  ⟨6, 4, 2, 3, 6, 3, -1465645974950828796522322752745600084598587392000000⟩,
  ⟨6, 4, 3, 3, 7, 3, -968789248434926558275454670365317357819763097600000⟩,
  ⟨6, 4, 4, 3, 8, 3, -112557915006546117263899540252595692806875381760000⟩,
  ⟨6, 4, 0, 4, 3, 3, 40701956758752260310366179168355542257110299443200000⟩,
  ⟨6, 4, 1, 4, 4, 3, -18271494363624780607838817773876396063475734937600000⟩,
  ⟨6, 4, 2, 4, 5, 3, -680674176768234559399347755145551892173763379200000⟩,
  ⟨6, 4, 3, 4, 6, 3, -2225321062715394097245094970414345128283367014400000⟩,
  ⟨6, 4, 4, 4, 7, 3, -256495357337813419697550066174231428284872130560000⟩,
  ⟨6, 4, 5, 4, 8, 3, 185745039915321442757214790008253540074101145600000⟩,
  ⟨6, 4, 0, 5, 2, 3, -68693026219111189412042997006217767741487998566400000⟩,
  ⟨6, 4, 1, 5, 3, 3, -34893897903006188586435094582801100996582414745600000⟩,
  ⟨6, 4, 2, 5, 4, 3, 3609093295002537147771977549073132849591641702400000⟩,
  ⟨6, 4, 3, 5, 5, 3, -731356165333201403916433583200858343918587084800000⟩,
  ⟨6, 4, 4, 5, 6, 3, 235277751519746122192478401319708989396699054080000⟩,
  ⟨6, 4, 5, 5, 7, 3, -6318756287815387668166388248529707490240102400000⟩,
  ⟨6, 4, 6, 5, 8, 3, 37376070317705926498856338301341328855374233600000⟩,
  ⟨6, 4, 0, 6, 1, 3, 49930510539753230178122241011567753555173441536000000⟩,
  ⟨6, 4, 1, 6, 2, 3, 86952752009391810029002436559789321078211765862400000⟩,
  ⟨6, 4, 2, 6, 3, 3, 1821084431945750575418023407312490732556648448000000⟩,
  ⟨6, 4, 3, 6, 4, 3, 3450545415286251416272660061309593361145082675200000⟩,
  ⟨6, 4, 4, 6, 5, 3, -381757832923361096522517328719636507480702320640000⟩,
  ⟨6, 4, 5, 6, 6, 3, 60102648160150189951330009375737748664195481600000⟩,
  ⟨6, 4, 6, 6, 7, 3, 35297839155488954829598877034826725834778214400000⟩,
  ⟨6, 4, 7, 6, 8, 3, 4840441150439118670235191410865511481527500800000⟩,
  ⟨6, 4, 0, 7, 0, 3, -486986721452998955566356947061559888164854484172800000⟩,
  ⟨6, 4, 1, 7, 1, 3, -248821782023095691203331058182337430072938882662400000⟩,
  ⟨6, 4, 2, 7, 2, 3, -8807845144640791275482152658321720857242422476800000⟩,
  ⟨6, 4, 3, 7, 3, 3, -6149588297645876157094103992923986570732214681600000⟩,
  ⟨6, 4, 4, 7, 4, 3, -1578802794657083554162649009726262523081292513280000⟩,
  ⟨6, 4, 5, 7, 5, 3, -67970106072873385081990154863357725251312025600000⟩,
  ⟨6, 4, 6, 7, 6, 3, -38203551868556505045968840578148274983141376000000⟩,
  ⟨6, 4, 7, 7, 7, 3, -1710769897427389457605491733304580761871974400000⟩,
  ⟨6, 4, 8, 7, 8, 3, -5100456681840644369861251364416517969018880000000⟩
]

def collectedFourData_9_7_31 : List CollectedFourTerm := [
  ⟨6, 5, 0, 0, 7, 4, -7591347653824121985188309732773923356838513868800000⟩,
  ⟨6, 5, 1, 0, 8, 4, -291170252867654088191495381020038755917391462400000⟩,
  ⟨6, 5, 0, 1, 6, 4, -955079162476776407642982145574260165730264678400000⟩,
  ⟨6, 5, 1, 1, 7, 4, -3053413549715916565343013062879167426574313062400000⟩,
  ⟨6, 5, 2, 1, 8, 4, 419760773283985005779011574962663455704324505600000⟩,
  ⟨6, 5, 0, 2, 5, 4, 4619191202488722711230217672263981290578404966400000⟩,
  ⟨6, 5, 1, 2, 6, 4, -3620780796638499511854593007138101711607536025600000⟩,
  ⟨6, 5, 2, 2, 7, 4, 510237341771309979551811491554297599575143219200000⟩,
  ⟨6, 5, 3, 2, 8, 4, 42926967441552385198195740445742248101308006400000⟩,
  ⟨6, 5, 0, 3, 4, 4, -2933452736085965633645256609812250915299445964800000⟩,
  ⟨6, 5, 1, 3, 5, 4, -2991323517154772017017936874788384721044347289600000⟩,
  ⟨6, 5, 2, 3, 6, 4, 202693257112099985566389320739853137050861568000000⟩,
  ⟨6, 5, 3, 3, 7, 4, 107183891104151057252605575559386745167748792320000⟩,
  ⟨6, 5, 4, 3, 8, 4, 10377554014337905262376345799207597825704591360000⟩,
  ⟨6, 5, 0, 4, 3, 4, -11257851250939543856613215456460916457393985945600000⟩,
  ⟨6, 5, 1, 4, 4, 4, 3369170789458195954478127430053562677437084467200000⟩,
  ⟨6, 5, 2, 4, 5, 4, 94134646619474035152979004892603983495744716800000⟩,
  ⟨6, 5, 3, 4, 6, 4, 246202743107632419400760386741916215049013166080000⟩,
  ⟨6, 5, 4, 4, 7, 4, 23648220785230937444445533572537942085373788160000⟩,
  ⟨6, 5, 5, 4, 8, 4, -14678760970077326319149234521772035693923532800000⟩,
  ⟨6, 5, 0, 5, 2, 4, 18999967882019606430731591686398058676136129331200000⟩,
  ⟨6, 5, 1, 5, 3, 4, 6434257603975325668876672868810691834809627443200000⟩,
  ⟨6, 5, 2, 5, 4, 4, -499123859163907508334296984149173910518733209600000⟩,
  ⟨6, 5, 3, 5, 5, 4, 80915018111587532261734467372390704741728911360000⟩,
  ⟨6, 5, 4, 5, 6, 4, -21692011393655782542750277268878145287492730880000⟩,
  ⟨6, 5, 5, 5, 7, 4, 499348532909946443589307421361907277443891200000⟩,
  ⟨6, 5, 6, 5, 8, 4, -2584484097873929050404462382491964043113267200000⟩,
  ⟨6, 5, 0, 6, 1, 4, -13810398941548154806121519942512879919104524288000000⟩,
  ⟨6, 5, 1, 6, 2, 4, -16033645978966708346973108976484198194214653132800000⟩,
  ⟨6, 5, 2, 6, 3, 4, -251849042194249051498803985328717855868321792000000⟩,
  ⟨6, 5, 3, 6, 4, 4, -381757832923361096522517328719636507480702320640000⟩,
  ⟨6, 5, 4, 6, 5, 4, 35197103032055639254596128460288808973280215040000⟩,
  ⟨6, 5, 5, 6, 6, 4, -4749695638783677928538850905769596882308300800000⟩,
  ⟨6, 5, 6, 6, 7, 4, -2440778369989759962852447983775953630055628800000⟩,
  ⟨6, 5, 7, 6, 8, 4, -297517590471740625276784029795262334710579200000⟩,
  ⟨6, 5, 0, 7, 0, 4, 134696818233970775235590914972674209140863034982400000⟩,
  ⟨6, 5, 1, 7, 1, 4, 45881473244032908186771982281075403195912342732800000⟩,
  ⟨6, 5, 2, 7, 2, 4, 1218091442966731726920903517701459799407014707200000⟩,
  ⟨6, 5, 3, 7, 3, 4, 680371714998973173097261997856448174837853061120000⟩,
  ⟨6, 5, 4, 7, 4, 4, 145561609581953055883788064290294258032789422080000⟩,
  ⟨6, 5, 5, 7, 5, 4, 5371432478678057036837113743462288811936972800000⟩,
  ⟨6, 5, 6, 7, 6, 4, 2641702871578029929160145303431180296650752000000⟩,
  ⟨6, 5, 7, 7, 7, 4, 105152427622843710917866259484352913709465600000⟩,
  ⟨6, 5, 8, 7, 8, 4, 282149494562938545440460813142923524702208000000⟩
]

def collectedFourData_9_7_32 : List CollectedFourTerm := [
  ⟨6, 6, 0, 0, 7, 5, 2390311646549860094746867647291305425102700544000000⟩,
  ⟨6, 6, 1, 0, 8, 5, 68761273850482203359308293290152289510621184000000⟩,
  ⟨6, 6, 0, 1, 6, 5, 300728796723635910333683729386938867218644992000000⟩,
  ⟨6, 6, 1, 1, 7, 5, 721078486565799304760641442451931187782877184000000⟩,
  ⟨6, 6, 2, 1, 8, 5, -79302841411040778059384027696653827411070156800000⟩,
  ⟨6, 6, 0, 2, 5, 5, -1454459344038527472585494146551032005559058432000000⟩,
  ⟨6, 6, 1, 2, 6, 5, 855065026245628661816712753983925683692240896000000⟩,
  ⟨6, 6, 2, 2, 7, 5, -96396027384641254300435914834017861729098137600000⟩,
  ⟨6, 6, 3, 2, 8, 5, -6758275006343595723449615571457324735266816000000⟩,
  ⟨6, 6, 0, 3, 4, 5, 923665541274167177327244481985763170555265024000000⟩,
  ⟨6, 6, 1, 3, 5, 5, 706415622862264358676489682630642650511835136000000⟩,
  ⟨6, 6, 2, 3, 6, 5, -38293600181104512530264224659924390619643904000000⟩,
  ⟨6, 6, 3, 3, 7, 5, -16874665402770920239248737102381388881775820800000⟩,
  ⟨6, 6, 4, 3, 8, 5, -1400405681065623463206500708466692810027827200000⟩,
  ⟨6, 6, 0, 4, 3, 5, 3544795231014215756798589945745328975671984128000000⟩,
  ⟨6, 6, 1, 4, 4, 5, -795646097159110683023630613122148149967716352000000⟩,
  ⟨6, 6, 2, 4, 5, 5, -17784284352597295239712521943409167318804070400000⟩,
  ⟨6, 6, 3, 4, 6, 5, -38761318220371652250051312299127854895149875200000⟩,
  ⟨6, 6, 4, 4, 7, 5, -3191224318271539892193003899994025307091763200000⟩,
  ⟨6, 6, 5, 4, 8, 5, 1733230460372661711877682876086528008781824000000⟩,
  ⟨6, 6, 0, 5, 2, 5, -5982579982302171045089699939652954101127315456000000⟩,
  ⟨6, 6, 1, 5, 3, 5, -1519481282082040067963118340238653868067520512000000⟩,
  ⟨6, 6, 2, 5, 4, 5, 94296424932882517612885929372350445161073868800000⟩,
  ⟨6, 6, 3, 5, 5, 5, -12738983840075463353026935440495634356266598400000⟩,
  ⟨6, 6, 4, 5, 6, 5, 2927242387507235916174811691806261717342617600000⟩,
  ⟨6, 6, 5, 5, 7, 5, -58961794482941321004267975642369119748096000000⟩,
  ⟨6, 6, 6, 5, 8, 5, 271261560800689946213744071873416986099712000000⟩,
  ⟨6, 6, 0, 6, 1, 5, 4348523995848501123213831343432189173238333440000000⟩,
  ⟨6, 6, 1, 6, 2, 5, 3786423616847049058604194225370660515923099648000000⟩,
  ⟨6, 6, 2, 6, 3, 5, 47580302695747507036409655374996812307890176000000⟩,
  ⟨6, 6, 3, 6, 4, 5, 60102648160150189951330009375737748664195481600000⟩,
  ⟨6, 6, 4, 6, 5, 5, -4749695638783677928538850905769596882308300800000⟩,
  ⟨6, 6, 5, 6, 6, 5, 560831883250953338402035450202791832715264000000⟩,
  ⟨6, 6, 6, 6, 7, 5, 256178535111374805805886881246714106216448000000⟩,
  ⟨6, 6, 7, 6, 8, 5, 28104091420440021136191033883480973692108800000⟩,
  ⟨6, 6, 0, 7, 0, 5, -42412413191968577591518470999799782548032192512000000⟩,
  ⟨6, 6, 1, 7, 1, 5, -10835133449674560315523815704905201855022235648000000⟩,
  ⟨6, 6, 2, 7, 2, 5, -230126583220257338883064415975053125045819801600000⟩,
  ⟨6, 6, 3, 7, 3, 5, -107115396929944515231392219965074163716902092800000⟩,
  ⟨6, 6, 4, 7, 4, 5, -19642904746338611597180021344950099348396441600000⟩,
  ⟨6, 6, 5, 7, 5, 5, -634244975230412269819086266891172550017024000000⟩,
  ⟨6, 6, 6, 7, 6, 5, -277267112885473176039739471242953930833920000000⟩,
  ⟨6, 6, 7, 7, 7, 5, -9932903242150651450281211835154944124518400000⟩,
  ⟨6, 6, 8, 7, 8, 5, -24229446482184171512793625890910025809920000000⟩
]

def collectedFourData_9_7_33 : List CollectedFourTerm := [
  ⟨6, 7, 0, 0, 7, 6, 2456671504082968420310104273573397944407687168000000⟩,
  ⟨6, 7, 1, 0, 8, 6, 56536180057273172242472687925345272535082598400000⟩,
  ⟨6, 7, 0, 1, 6, 6, 309077632799253173591676323581578279779303424000000⟩,
  ⟨6, 7, 1, 1, 7, 6, 592877660186398307975010140289509272498628198400000⟩,
  ⟨6, 7, 2, 1, 8, 6, -54336298495781616185074106532288894385677926400000⟩,
  ⟨6, 7, 0, 2, 5, 6, -1494838059925808150013943030486293266357551104000000⟩,
  ⟨6, 7, 1, 2, 6, 6, 703042680529992293358603181308327911898061209600000⟩,
  ⟨6, 7, 2, 2, 7, 6, -66048116619566464493710104311184529550003404800000⟩,
  ⟨6, 7, 3, 2, 8, 6, -3969084748259804815056482729961041789190144000000⟩,
  ⟨6, 7, 0, 3, 4, 6, 949308353924001525487152743616035550268489728000000⟩,
  ⟨6, 7, 1, 3, 5, 6, 580821712760222263561664666328351396660353433600000⟩,
  ⟨6, 7, 2, 3, 6, 6, -26237805012985650315026977514143332949819392000000⟩,
  ⟨6, 7, 3, 3, 7, 6, -9910365739668495593868397654444225422635827200000⟩,
  ⟨6, 7, 4, 3, 8, 6, -719641879291252522170640261889923575132979200000⟩,
  ⟨6, 7, 0, 4, 3, 6, 3643205874184396373105213851748681966961033216000000⟩,
  ⟨6, 7, 1, 4, 4, 6, -654187866104209682196538539634683175748449075200000⟩,
  ⟨6, 7, 2, 4, 5, 6, -12185341230182570722671547185834575726326579200000⟩,
  ⟨6, 7, 3, 4, 6, 6, -22764234486835014025108008804612170241068236800000⟩,
  ⟨6, 7, 4, 4, 7, 6, -1639909560987606838344895173351042800890675200000⟩,
  ⟨6, 7, 5, 4, 8, 6, 791710410212180941306930418206020225466368000000⟩,
  ⟨6, 7, 0, 5, 2, 6, -6148668431847662816354532242359307710425464832000000⟩,
  ⟨6, 7, 1, 5, 3, 6, -1249332110167765210723454134237050057681744691200000⟩,
  ⟨6, 7, 2, 5, 4, 6, 64609522194558201979255533215849962822592102400000⟩,
  ⟨6, 7, 3, 5, 5, 6, -7481510654791638858944257759052980798724505600000⟩,
  ⟨6, 7, 4, 5, 6, 6, 1504254261010817575387964910323756657383833600000⟩,
  ⟨6, 7, 5, 5, 7, 6, -26932752201284862471121485058108211331072000000⟩,
  ⟨6, 7, 6, 5, 8, 6, 111516930862801441108459474958918914513305600000⟩,
  ⟨6, 7, 0, 6, 1, 6, 4469247765596401305944806989607421483868487680000000⟩,
  ⟨6, 7, 1, 6, 2, 6, 3113233879882158090669711402328413419460152524800000⟩,
  ⟨6, 7, 2, 6, 3, 6, 32600818379199220519747517494013528478056448000000⟩,
  ⟨6, 7, 3, 6, 4, 6, 35297839155488954829598877034826725834778214400000⟩,
  ⟨6, 7, 4, 6, 5, 6, -2440778369989759962852447983775953630055628800000⟩,
  ⟨6, 7, 5, 6, 6, 6, 256178535111374805805886881246714106216448000000⟩,
  ⟨6, 7, 6, 6, 7, 6, 105316226538781580166373144998122118080102400000⟩,
  ⟨6, 7, 7, 6, 8, 6, 10503388184532730336169510913793851811430400000⟩,
  ⟨6, 7, 0, 7, 0, 6, -43589867061264968092893992191347502880982564864000000⟩,
  ⟨6, 7, 1, 7, 1, 6, -8908750832443871575745314938912471720619986124800000⟩,
  ⟨6, 7, 2, 7, 2, 6, -157676906592269416812470498822824412280835276800000⟩,
  ⟨6, 7, 3, 7, 3, 6, -62908077558160105058151280676199823609901875200000⟩,
  ⟨6, 7, 4, 7, 4, 6, -10094115639146547809474993198924241124825497600000⟩,
  ⟨6, 7, 5, 7, 5, 6, -289712396011503006369532163600371855392768000000⟩,
  ⟨6, 7, 6, 7, 6, 6, -113985842177234979098589854334912766672896000000⟩,
  ⟨6, 7, 7, 7, 7, 6, -3712240221216820177642391297727646610227200000⟩,
  ⟨6, 7, 8, 7, 8, 6, -8300701544977886274190411890983782318080000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0930
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0930. -/
namespace LaughlinFock
def collectedFourData_9_7_34 : List CollectedFourTerm := [
  ⟨6, 8, 0, 0, 7, 7, 539018778530535973621369039909471179570256281600000⟩,
  ⟨6, 8, 1, 0, 8, 7, 10337178667221816111011598725973620176610918400000⟩,
  ⟨6, 8, 0, 1, 6, 7, 67814784282586151680355205539498680531078348800000⟩,
  ⟨6, 8, 1, 1, 7, 7, 108402836819584331748477880915989345063036518400000⟩,
  ⟨6, 8, 2, 1, 8, 7, -8515669967151521235499947974662723858543411200000⟩,
  ⟨6, 8, 0, 2, 5, 7, -327982713123436399665707872354196525369052364800000⟩,
  ⟨6, 8, 1, 2, 6, 7, 128545610827595070482451709667063819633531289600000⟩,
  ⟨6, 8, 2, 2, 7, 7, -10351164482207572221716216884219753747867238400000⟩,
  ⟨6, 8, 3, 2, 8, 7, -544286041432354587594373643860744505131008000000⟩,
  ⟨6, 8, 0, 3, 4, 7, 208287932892336637854556270101256289998444953600000⟩,
  ⟨6, 8, 1, 3, 5, 7, 106198505320343213769987480188842724130658713600000⟩,
  ⟨6, 8, 2, 3, 6, 7, -4112029975144619994968075060353920072155136000000⟩,
  ⟨6, 8, 3, 3, 7, 7, -1359022061687132747537405510937480381490790400000⟩,
  ⟨6, 8, 4, 3, 8, 7, -87720425812437418891402376938476884774092800000⟩,
  ⟨6, 8, 0, 4, 3, 7, 799356518351924314774023628048615968477492019200000⟩,
  ⟨6, 8, 1, 4, 4, 7, -119612907115358474916174160989037785194378035200000⟩,
  ⟨6, 8, 2, 4, 5, 7, -1909705799363840755980090195186810369972633600000⟩,
  ⟨6, 8, 3, 4, 6, 7, -3121690732481756354260320853724059389237657600000⟩,
  ⟨6, 8, 4, 4, 7, 7, -199896044301084867049544796356755006999756800000⟩,
  ⟨6, 8, 5, 4, 8, 7, 86854668512503525119279419818277916691660800000⟩,
  ⟨6, 8, 0, 5, 2, 7, -1349080551557479295839516655018070948801046118400000⟩,
  ⟨6, 8, 1, 5, 3, 7, -228430170280668376065246927575302874240070451200000⟩,
  ⟨6, 8, 2, 5, 4, 7, 10125705706415077926644031438652285574656819200000⟩,
  ⟨6, 8, 3, 5, 5, 7, -1025949828865679222485123146420021256991539200000⟩,
  ⟨6, 8, 4, 5, 6, 7, 183360402032186507762185744109059873072742400000⟩,
  ⟨6, 8, 5, 5, 7, 7, -2954660232325445560758098427134935774003200000⟩,
  ⟨6, 8, 6, 5, 8, 7, 11121796255854089119433303884811801827737600000⟩,
  ⟨6, 8, 0, 6, 1, 7, 980598532428265865784963778603839363288662016000000⟩,
  ⟨6, 8, 1, 6, 2, 7, 569229382257316961726062186627224374245903564800000⟩,
  ⟨6, 8, 2, 6, 3, 7, 5109251415016076581742880019404731222851584000000⟩,
  ⟨6, 8, 3, 6, 4, 7, 4840441150439118670235191410865511481527500800000⟩,
  ⟨6, 8, 4, 6, 5, 7, -297517590471740625276784029795262334710579200000⟩,
  ⟨6, 8, 5, 6, 6, 7, 28104091420440021136191033883480973692108800000⟩,
  ⟨6, 8, 6, 6, 7, 7, 10503388184532730336169510913793851811430400000⟩,
  ⟨6, 8, 7, 6, 8, 7, 960229362548996560846139296932781306675200000⟩,
  ⟨6, 8, 0, 7, 0, 7, -9564061316550351348004973508810525688900406476800000⟩,
  ⟨6, 8, 1, 7, 1, 7, -1628892312205061523964762058140513792431017164800000⟩,
  ⟨6, 8, 2, 7, 2, 7, -24711372234628504175682788586289704452122214400000⟩,
  ⟨6, 8, 3, 7, 3, 7, -8626671053890345421656722249706146885953126400000⟩,
  ⟨6, 8, 4, 7, 4, 7, -1230417722406559390931666437543664065865318400000⟩,
  ⟨6, 8, 5, 7, 5, 7, -31782926932587018366766018689908228279500800000⟩,
  ⟨6, 8, 6, 7, 6, 7, -11368025491185942152584224895899864662016000000⟩,
  ⟨6, 8, 7, 7, 7, 7, -339376399179171488774741406577352874393600000⟩,
  ⟨6, 8, 8, 7, 8, 7, -700484061820477247638816521840450600960000000⟩
]

def collectedFourData_9_7_35 : List CollectedFourTerm := [
  ⟨7, 0, 2, 1, 8, 0, 107092981543187298551581665309130111515122624102400000⟩,
  ⟨7, 0, 2, 2, 7, 0, 130176142466727772848482390943490868708771679436800000⟩,
  ⟨7, 0, 3, 2, 8, 0, 54759487123550215883037923823222380843633737728000000⟩,
  ⟨7, 0, 2, 3, 6, 0, 51712848423187384952229314689958760505694748672000000⟩,
  ⟨7, 0, 3, 3, 7, 0, 136728384383574644393093960604350055966411482726400000⟩,
  ⟨7, 0, 4, 3, 8, 0, 39714163563672375903104856799721158467892386201600000⟩,
  ⟨7, 0, 2, 4, 5, 0, 24016441303278908940993969222688204015919117107200000⟩,
  ⟨7, 0, 3, 4, 6, 0, 314066814976892913684097643996028937600050502041600000⟩,
  ⟨7, 0, 4, 4, 7, 0, 90500064558268440359686661014412312161067571609600000⟩,
  ⟨7, 0, 5, 4, 8, 0, -131074014580119345698535943010998955629181140992000000⟩,
  ⟨7, 0, 2, 5, 4, 0, -127340775125363828643904694466001033222777366118400000⟩,
  ⟨7, 0, 3, 5, 5, 0, 103218679456362613905384327938185027326812828467200000⟩,
  ⟨7, 0, 4, 5, 6, 0, -83013789889452433518411984705537802816562449612800000⟩,
  ⟨7, 0, 5, 5, 7, 0, 4458933353886117008548119971549369655380410368000000⟩,
  ⟨7, 0, 6, 5, 8, 0, -46156308017737197571158609637330730494004822016000000⟩,
  ⟨7, 0, 2, 6, 3, 0, -64253895418500599130495660303672281606041632768000000⟩,
  ⟨7, 0, 3, 6, 4, 0, -486986721452998955566356947061559888164854484172800000⟩,
  ⟨7, 0, 4, 6, 5, 0, 134696818233970775235590914972674209140863034982400000⟩,
  ⟨7, 0, 5, 6, 6, 0, -42412413191968577591518470999799782548032192512000000⟩,
  ⟨7, 0, 6, 6, 7, 0, -43589867061264968092893992191347502880982564864000000⟩,
  ⟨7, 0, 7, 6, 8, 0, -9564061316550351348004973508810525688900406476800000⟩,
  ⟨7, 0, 2, 7, 2, 0, 310769973570866689862581977935230405616419523788800000⟩,
  ⟨7, 0, 3, 7, 3, 0, 867911440924435259388738338462416778506243827302400000⟩,
  ⟨7, 0, 4, 7, 4, 0, 557053961226519940147667921190068069063799393484800000⟩,
  ⟨7, 0, 5, 7, 5, 0, 47964213087302922985388408525286015202693742592000000⟩,
  ⟨7, 0, 6, 7, 6, 0, 47178178241530120233731706334168806232487362560000000⟩,
  ⟨7, 0, 7, 7, 7, 0, 3380251445887277532451312859845144879995184742400000⟩,
  ⟨7, 0, 8, 7, 8, 0, 15116725603545715685760063230752929878869278720000000⟩
]

def collectedFourData_9_7_36 : List CollectedFourTerm := [
  ⟨7, 1, 1, 0, 8, 1, -18977868937450069109197746568669718156021229158400000⟩,
  ⟨7, 1, 1, 1, 7, 1, -199015117745155383362253585606832805748647814758400000⟩,
  ⟨7, 1, 2, 1, 8, 1, 109436521925019984069387663440111328929081878118400000⟩,
  ⟨7, 1, 1, 2, 6, 1, -235994929884113057626650475333870920035498301849600000⟩,
  ⟨7, 1, 2, 2, 7, 1, 133024816975794034270116109421168957693769862348800000⟩,
  ⟨7, 1, 3, 2, 8, 1, 27978900796512918159929528022892489572429594624000000⟩,
  ⟨7, 1, 1, 3, 5, 1, -194968219105399765974562314763906256401390475673600000⟩,
  ⟨7, 1, 2, 3, 6, 1, 52844492596250768182208582328468875556685873152000000⟩,
  ⟨7, 1, 3, 3, 7, 1, 69860221555842471712752111533896803319977030451200000⟩,
  ⟨7, 1, 4, 3, 8, 1, 13527745917432760193343388829864414176529822515200000⟩,
  ⟨7, 1, 1, 4, 4, 1, 219595515134182997876461520942321087739241640755200000⟩,
  ⟨7, 1, 2, 4, 5, 1, 24541998620024741934046357182636647907658511155200000⟩,
  ⟨7, 1, 3, 4, 6, 1, 160469805714016007827827239432694522287208844492800000⟩,
  ⟨7, 1, 4, 4, 7, 1, 30826832771958030639201831708614653803077251891200000⟩,
  ⟨7, 1, 5, 4, 8, 1, -33485584357862452735775352349018881007779053568000000⟩,
  ⟨7, 1, 1, 5, 3, 1, 419371471898049081094919873645300454436614910771200000⟩,
  ⟨7, 1, 2, 5, 4, 1, -130127402637828951063565344839682300757246633574400000⟩,
  ⟨7, 1, 3, 5, 5, 1, 52738718796630717666886768585237721166420482457600000⟩,
  ⟨7, 1, 4, 5, 6, 1, -28276799924722324027127793571509846532320500121600000⟩,
  ⟨7, 1, 5, 5, 7, 1, 1139127304873797008763963052485555485379919872000000⟩,
  ⟨7, 1, 6, 5, 8, 1, -9433271427454067014594120855735824516436407091200000⟩,
  ⟨7, 1, 1, 6, 2, 1, -1045039556690601259546517747795752977575900400844800000⟩,
  ⟨7, 1, 2, 6, 3, 1, -65659978211541386955992164687685860593015717888000000⟩,
  ⟨7, 1, 3, 6, 4, 1, -248821782023095691203331058182337430072938882662400000⟩,
  ⟨7, 1, 4, 6, 5, 1, 45881473244032908186771982281075403195912342732800000⟩,
  ⟨7, 1, 5, 6, 6, 1, -10835133449674560315523815704905201855022235648000000⟩,
  ⟨7, 1, 6, 6, 7, 1, -8908750832443871575745314938912471720619986124800000⟩,
  ⟨7, 1, 7, 6, 8, 1, -1628892312205061523964762058140513792431017164800000⟩,
  ⟨7, 1, 1, 7, 1, 1, 2990458597012496164648850317601466414100942474444800000⟩,
  ⟨7, 1, 2, 7, 2, 1, 317570624482156341164065498589243678095594802380800000⟩,
  ⟨7, 1, 3, 7, 3, 1, 443452073446099975077858985151177291571678884659200000⟩,
  ⟨7, 1, 4, 7, 4, 1, 189748033788753830308983165236333481949539178905600000⟩,
  ⟨7, 1, 5, 7, 5, 1, 12253456252472021466487253946786720633971539968000000⟩,
  ⟨7, 1, 6, 7, 6, 1, 9642117836507571043990987364128878646989422592000000⟩,
  ⟨7, 1, 7, 7, 7, 1, 575703711141806589252072759063176936262362726400000⟩,
  ⟨7, 1, 8, 7, 8, 1, 2206789770251863724793431350673327502246543360000000⟩
]

def collectedFourData_9_7_37 : List CollectedFourTerm := [
  ⟨7, 2, 0, 0, 7, 2, -17514614975153126476461120880040940221136214425600000⟩,
  ⟨7, 2, 1, 0, 8, 2, -2015347644614573190772509750888503025877804646400000⟩,
  ⟨7, 2, 0, 1, 6, 2, -2203540736689334138121083115947489034534440140800000⟩,
  ⟨7, 2, 1, 1, 7, 2, -21134335478463997922980429409975612063734982246400000⟩,
  ⟨7, 2, 2, 1, 8, 2, 5810785115634651520203951231348216150583620403200000⟩,
  ⟨7, 2, 0, 2, 5, 2, 10657311336209151474689564375787690724988603596800000⟩,
  ⟨7, 2, 1, 2, 6, 2, -25061392701705179981031343665348723848985024921600000⟩,
  ⟨7, 2, 2, 2, 7, 2, 7063260170334827088665112924559066225392903782400000⟩,
  ⟨7, 2, 3, 2, 8, 2, 990402944345437704914108899690984101818400768000000⟩,
  ⟨7, 2, 0, 3, 4, 2, -6768007152784457303420411098553548476679559577600000⟩,
  ⟨7, 2, 1, 3, 5, 2, -20704576601505431515904709041116178243550550425600000⟩,
  ⟨7, 2, 2, 3, 6, 2, 2805900494827000897588391917592159431893712896000000⟩,
  ⟨7, 2, 3, 3, 7, 2, 2472926639425173434967603067221046481176127078400000⟩,
  ⟨7, 2, 4, 3, 8, 2, 359143470764553686998930141912721864822410444800000⟩,
  ⟨7, 2, 0, 4, 3, 2, -25973903330382283042776485766533356008355607347200000⟩,
  ⟨7, 2, 1, 4, 4, 2, 23319863028470445541822026498877340015320576819200000⟩,
  ⟨7, 2, 2, 4, 5, 2, 1303114150382752915431833930298967033422387609600000⟩,
  ⟨7, 2, 3, 4, 6, 2, 5680343527916923039779701830010596136435947929600000⟩,
  ⟨7, 2, 4, 4, 7, 2, 818410974154410471325812985711706338396785868800000⟩,
  ⟨7, 2, 5, 4, 8, 2, -711197803995670503035903177255042323049978265600000⟩,
  ⟨7, 2, 0, 5, 2, 2, 43836369663061525734576327292303316472031503974400000⟩,
  ⟨7, 2, 1, 5, 3, 2, 44534995519989139949373046462941991910103003955200000⟩,
  ⟨7, 2, 2, 5, 4, 2, -6909415258117960152145728128255810496156087091200000⟩,
  ⟨7, 2, 3, 5, 5, 2, 1866856126946167311105889939353451213276525363200000⟩,
  ⟨7, 2, 4, 5, 6, 2, -750711029691404871925959470614686927713363558400000⟩,
  ⟨7, 2, 5, 5, 7, 2, 24193839027555395362703800888708613802452582400000⟩,
  ⟨7, 2, 6, 5, 8, 2, -166960451100434359126851018151054443428393779200000⟩,
  ⟨7, 2, 0, 6, 1, 2, -31863093503908998713152946046006430150170771456000000⟩,
  ⟨7, 2, 1, 6, 2, 2, -110977582153565348898929645100816602928429976780800000⟩,
  ⟨7, 2, 2, 6, 3, 2, -3486368329084217153516304201227000986441089024000000⟩,
  ⟨7, 2, 3, 6, 4, 2, -8807845144640791275482152658321720857242422476800000⟩,
  ⟨7, 2, 4, 6, 5, 2, 1218091442966731726920903517701459799407014707200000⟩,
  ⟨7, 2, 5, 6, 6, 2, -230126583220257338883064415975053125045819801600000⟩,
  ⟨7, 2, 6, 6, 7, 2, -157676906592269416812470498822824412280835276800000⟩,
  ⟨7, 2, 7, 6, 8, 2, -24711372234628504175682788586289704452122214400000⟩,
  ⟨7, 2, 0, 7, 0, 2, 310769973570866689862581977935230405616419523788800000⟩,
  ⟨7, 2, 1, 7, 1, 2, 317570624482156341164065498589243678095594802380800000⟩,
  ⟨7, 2, 2, 7, 2, 2, 16862146433784137786909793030259265498658530918400000⟩,
  ⟨7, 2, 3, 7, 3, 2, 15697408644153913857304078249520741500169119334400000⟩,
  ⟨7, 2, 4, 7, 4, 2, 5037555246940612910707781758211382687820047974400000⟩,
  ⟨7, 2, 5, 7, 5, 2, 260250234398818689551304038576103307739765145600000⟩,
  ⟨7, 2, 6, 7, 6, 2, 170656845393171215452482659765669803088412672000000⟩,
  ⟨7, 2, 7, 7, 7, 2, 8733805541523889578216539731122954173625139200000⟩,
  ⟨7, 2, 8, 7, 8, 2, 29293651069932795632559579756508110724792320000000⟩
]

def collectedFourData_9_7_38 : List CollectedFourTerm := [
  ⟨7, 3, 0, 0, 7, 3, -48914425501456750088885123375909740575718165708800000⟩,
  ⟨7, 3, 1, 0, 8, 3, -2814208943841599196090071235112105914456971673600000⟩,
  ⟨7, 3, 0, 1, 6, 3, -6153999351805518024005469580427207155141469798400000⟩,
  ⟨7, 3, 1, 1, 7, 3, -29511750037059648961190161777620779115954674073600000⟩,
  ⟨7, 3, 2, 1, 8, 3, 5409410294334297556601188725606903770650981171200000⟩,
  ⟨7, 3, 0, 2, 5, 3, 29763501061277280599687103588900792044205008486400000⟩,
  ⟨7, 3, 1, 2, 6, 3, -34995448886811526258847082304289346068286957158400000⟩,
  ⟨7, 3, 2, 2, 7, 3, 6575371746954984072166201618918304788018259558400000⟩,
  ⟨7, 3, 3, 2, 8, 3, 691493805406715548131154088167684661959458816000000⟩,
  ⟨7, 3, 0, 3, 4, 3, -18901539208132516955249222974395674131897830604800000⟩,
  ⟨7, 3, 1, 3, 5, 3, -28911639540756953937877374770195559308721546854400000⟩,
  ⟨7, 3, 2, 3, 6, 3, 2612085410068913571870368925277567085954727936000000⟩,
  ⟨7, 3, 3, 3, 7, 3, 1726583571010999376492326099241979967764745420800000⟩,
  ⟨7, 3, 4, 3, 8, 3, 200601572686227829412256375603954721365247918080000⟩,
  ⟨7, 3, 0, 4, 3, 3, -72539337075830630031293863882206624805820144025600000⟩,
  ⟨7, 3, 1, 4, 4, 3, 32563596300246974239353938490443942979206696140800000⟩,
  ⟨7, 3, 2, 4, 5, 3, 1213102697741604245497148921299925946118805913600000⟩,
  ⟨7, 3, 3, 4, 6, 3, 3965984132582183047018946476378729681974932275200000⟩,
  ⟨7, 3, 4, 4, 7, 3, 457127977767613641450243778302905586561822228480000⟩,
  ⟨7, 3, 5, 4, 8, 3, -331036223649955153566749836752569815106637004800000⟩,
  ⟨7, 3, 0, 5, 2, 3, 122425234079083442320368481543500765982046237491200000⟩,
  ⟨7, 3, 1, 5, 3, 3, 62188170384007359394664359407795840629756185804800000⟩,
  ⟨7, 3, 2, 5, 4, 3, -6432153535419728790330833524353448894885212979200000⟩,
  ⟨7, 3, 3, 5, 5, 3, 1303428523450142651651832489024589247145207398400000⟩,
  ⟨7, 3, 4, 5, 6, 3, -419313799213460240331249041916014556669951344640000⟩,
  ⟨7, 3, 5, 5, 7, 3, 11261335541645735006662653728979569647760179200000⟩,
  ⟨7, 3, 6, 5, 8, 3, -66611916950725308619421866395875359534664908800000⟩,
  ⟨7, 3, 0, 6, 1, 3, -88986535853282783679370929771788110788651122688000000⟩,
  ⟨7, 3, 1, 6, 2, 3, -154967856338358047666788965973177219812026430259200000⟩,
  ⟨7, 3, 2, 6, 3, 3, -3245550532998746882299862536518897303010934784000000⟩,
  ⟨7, 3, 3, 6, 4, 3, -6149588297645876157094103992923986570732214681600000⟩,
  ⟨7, 3, 4, 6, 5, 3, 680371714998973173097261997856448174837853061120000⟩,
  ⟨7, 3, 5, 6, 6, 3, -107115396929944515231392219965074163716902092800000⟩,
  ⟨7, 3, 6, 6, 7, 3, -62908077558160105058151280676199823609901875200000⟩,
  ⟨7, 3, 7, 6, 8, 3, -8626671053890345421656722249706146885953126400000⟩,
  ⟨7, 3, 0, 7, 0, 3, 867911440924435259388738338462416778506243827302400000⟩,
  ⟨7, 3, 1, 7, 1, 3, 443452073446099975077858985151177291571678884659200000⟩,
  ⟨7, 3, 2, 7, 2, 3, 15697408644153913857304078249520741500169119334400000⟩,
  ⟨7, 3, 3, 7, 3, 3, 10959843062203496465120366622069125441055935692800000⟩,
  ⟨7, 3, 4, 7, 4, 3, 2813754355268604707065806666908915682760709898240000⟩,
  ⟨7, 3, 5, 7, 5, 3, 121136840293062908976064826878839647774756044800000⟩,
  ⟨7, 3, 6, 7, 6, 3, 68086660867755141799647569405833509662097408000000⟩,
  ⟨7, 3, 7, 7, 7, 3, 3048947130090604725063642859352642148315955200000⟩,
  ⟨7, 3, 8, 7, 8, 3, 9090072712662701241075742274243227853783040000000⟩
]

def collectedFourData_9_7_39 : List CollectedFourTerm := [
  ⟨7, 4, 0, 0, 7, 4, -31394878788190018244384088139163307601882093977600000⟩,
  ⟨7, 4, 1, 0, 8, 4, -1204167588201780406810618231645758267100810444800000⟩,
  ⟨7, 4, 0, 1, 6, 4, -3949838145533984701432983395786528774020713676800000⟩,
  ⟨7, 4, 1, 1, 7, 4, -12627737874085928162949261878834159743910333644800000⟩,
  ⟨7, 4, 2, 1, 8, 4, 1735968262584979330343526802024144076381827891200000⟩,
  ⟨7, 4, 0, 2, 5, 4, 19103188855875177784517635954432988224047336652800000⟩,
  ⟨7, 4, 1, 2, 6, 4, -14974149441279877407703144838321703885881946931200000⟩,
  ⟨7, 4, 2, 2, 7, 4, 2110144368114811730151407749415528312412202598400000⟩,
  ⟨7, 4, 3, 2, 8, 4, 177529340115680601492051307847219655184534732800000⟩,
  ⟨7, 4, 0, 3, 4, 4, -12131626330393449335570112411484807636870338969600000⟩,
  ⟨7, 4, 1, 3, 5, 4, -12370957505816277769513641237693635581988516659200000⟩,
  ⟨7, 4, 2, 3, 6, 4, 838260942378551362060699054882316498591809536000000⟩,
  ⟨7, 4, 3, 3, 7, 4, 443271132177204127773453626360318886813515120640000⟩,
  ⟨7, 4, 4, 3, 8, 4, 42917551040349380376104467834563777251738910720000⟩,
  ⟨7, 4, 0, 4, 3, 4, -46558120054042896736117798185511633519620862771200000⟩,
  ⟨7, 4, 1, 4, 4, 4, 13933587733722983285761594470500361632234235494400000⟩,
  ⟨7, 4, 2, 4, 5, 4, 389304502330194387545100239980457429516786073600000⟩,
  ⟨7, 4, 3, 4, 6, 4, 1018199354009335446886334665445293720384737116160000⟩,
  ⟨7, 4, 4, 4, 7, 4, 97799897852745858045974023381755821975477944320000⟩,
  ⟨7, 4, 5, 4, 8, 4, -60705679996653329618631284074512022226180505600000⟩,
  ⟨7, 4, 0, 5, 2, 4, 78576521039057243999029407133384899842898552422400000⟩,
  ⟨7, 4, 1, 5, 3, 4, 26609601717691972611121300282050748196707526246400000⟩,
  ⟨7, 4, 2, 5, 4, 4, -2064183300951947991134086530798855330316104499200000⟩,
  ⟨7, 4, 3, 5, 5, 4, 334633230040230376134024311414899813254923550720000⟩,
  ⟨7, 4, 4, 5, 6, 4, -89709772155250854709833324776301027806423285760000⟩,
  ⟨7, 4, 5, 5, 7, 4, 2065112464698022474241339654958935926269542400000⟩,
  ⟨7, 4, 6, 5, 8, 4, -10688426967494076182929512492765480080533094400000⟩,
  ⟨7, 4, 0, 6, 1, 4, -57114470388935401091484333447247049598462590976000000⟩,
  ⟨7, 4, 1, 6, 2, 4, -66308960542577250756618165852978940796401719705600000⟩,
  ⟨7, 4, 2, 6, 3, 4, -1041550263954409619518576688083176870257885184000000⟩,
  ⟨7, 4, 3, 6, 4, 4, -1578802794657083554162649009726262523081292513280000⟩,
  ⟨7, 4, 4, 6, 5, 4, 145561609581953055883788064290294258032789422080000⟩,
  ⟨7, 4, 5, 6, 6, 4, -19642904746338611597180021344950099348396441600000⟩,
  ⟨7, 4, 6, 6, 7, 4, -10094115639146547809474993198924241124825497600000⟩,
  ⟨7, 4, 7, 6, 8, 4, -1230417722406559390931666437543664065865318400000⟩,
  ⟨7, 4, 0, 7, 0, 4, 557053961226519940147667921190068069063799393484800000⟩,
  ⟨7, 4, 1, 7, 1, 4, 189748033788753830308983165236333481949539178905600000⟩,
  ⟨7, 4, 2, 7, 2, 4, 5037555246940612910707781758211382687820047974400000⟩,
  ⟨7, 4, 3, 7, 3, 4, 2813754355268604707065806666908915682760709898240000⟩,
  ⟨7, 4, 4, 7, 4, 4, 601986537494062065575638839076358280137838428160000⟩,
  ⟨7, 4, 5, 7, 5, 4, 22214167928680618039874001120802476251519385600000⟩,
  ⟨7, 4, 6, 7, 6, 4, 10925061692547697119845432882129990376751104000000⟩,
  ⟨7, 4, 7, 7, 7, 4, 434869784660712654835272081700966651605811200000⟩,
  ⟨7, 4, 8, 7, 8, 4, 1166861219626835899047302453829373123362816000000⟩
]

def collectedFourData_9_7_40 : List CollectedFourTerm := [
  ⟨7, 5, 0, 0, 7, 5, -2703204286944228247293543367688381834937237504000000⟩,
  ⟨7, 5, 1, 0, 8, 5, -77762148930102836389180846180838084123295744000000⟩,
  ⟨7, 5, 0, 1, 6, 5, -340094302633836428829192673513433879933878272000000⟩,
  ⟨7, 5, 1, 1, 7, 5, -815467915625731554431332198522909661010591744000000⟩,
  ⟨7, 5, 2, 1, 8, 5, 89683611414689255483016725752321391102577868800000⟩,
  ⟨7, 5, 0, 2, 5, 5, 1644848586863556205250578649394125294442381312000000⟩,
  ⟨7, 5, 1, 2, 6, 5, -966993340763546356611553906295464884789313536000000⟩,
  ⟨7, 5, 2, 2, 7, 5, 109014301481009831066899658002294859892365721600000⟩,
  ⟨7, 5, 3, 2, 8, 5, 7642935596228732937847765113851364828512256000000⟩,
  ⟨7, 5, 0, 3, 4, 5, -1044573687485025257323152128478275973817565184000000⟩,
  ⟨7, 5, 1, 3, 5, 5, -798885677874647661297999410048949362544869376000000⟩,
  ⟨7, 5, 2, 3, 6, 5, 43306245995789963590772196119449661041803264000000⟩,
  ⟨7, 5, 3, 3, 7, 5, 19083565075441427482939383574079173330521292800000⟩,
  ⟨7, 5, 4, 3, 8, 5, 1583719280279497479897884842235775507706675200000⟩,
  ⟨7, 5, 0, 4, 3, 5, -4008810181152754674178952121524597324563611648000000⟩,
  ⟨7, 5, 1, 4, 4, 5, 899796452832991710770720505319886283218092032000000⟩,
  ⟨7, 5, 2, 4, 5, 5, 20112253467687468971276379894653645043951206400000⟩,
  ⟨7, 5, 3, 4, 6, 5, 43835188491908830177636708133039488214709043200000⟩,
  ⟨7, 5, 4, 4, 7, 5, 3608956710813715214694980290149999245996851200000⟩,
  ⟨7, 5, 5, 4, 8, 5, -1960110940974727890695543773925140001193984000000⟩,
  ⟨7, 5, 0, 5, 2, 5, 6765701819044630335171473942120468017626218496000000⟩,
  ⟨7, 5, 1, 5, 3, 5, 1718381919606316145602409177751957761364590592000000⟩,
  ⟨7, 5, 2, 5, 4, 5, -106639860325328318416170580868657607659539660800000⟩,
  ⟨7, 5, 3, 5, 5, 5, 14406521332693062692790893453343332262897254400000⟩,
  ⟨7, 5, 4, 5, 6, 5, -3310419451896922389886685485675120879573401600000⟩,
  ⟨7, 5, 5, 5, 7, 5, 66679914245603311896489152553741226868736000000⟩,
  ⟨7, 5, 6, 5, 8, 5, -306769795100988690859326569756052833697792000000⟩,
  ⟨7, 5, 0, 6, 1, 5, -4917747325719819809387287627441714658059223040000000⟩,
  ⟨7, 5, 1, 6, 2, 5, -4282067808196285191085986991104095880078163968000000⟩,
  ⟨7, 5, 2, 6, 3, 5, -53808581155890619495466044586450297359958016000000⟩,
  ⟨7, 5, 3, 6, 4, 5, -67970106072873385081990154863357725251312025600000⟩,
  ⟨7, 5, 4, 6, 5, 5, 5371432478678057036837113743462288811936972800000⟩,
  ⟨7, 5, 5, 6, 6, 5, -634244975230412269819086266891172550017024000000⟩,
  ⟨7, 5, 6, 6, 7, 5, -289712396011503006369532163600371855392768000000⟩,
  ⟨7, 5, 7, 6, 8, 5, -31782926932587018366766018689908228279500800000⟩,
  ⟨7, 5, 0, 7, 0, 5, 47964213087302922985388408525286015202693742592000000⟩,
  ⟨7, 5, 1, 7, 1, 5, 12253456252472021466487253946786720633971539968000000⟩,
  ⟨7, 5, 2, 7, 2, 5, 260250234398818689551304038576103307739765145600000⟩,
  ⟨7, 5, 3, 7, 3, 5, 121136840293062908976064826878839647774756044800000⟩,
  ⟨7, 5, 4, 7, 4, 5, 22214167928680618039874001120802476251519385600000⟩,
  ⟨7, 5, 5, 7, 5, 5, 717267866928716511541517933626308043997184000000⟩,
  ⟨7, 5, 6, 7, 6, 5, 313561476078858302016974282252461245726720000000⟩,
  ⟨7, 5, 7, 7, 7, 5, 11233123791510497524748827846631745807974400000⟩,
  ⟨7, 5, 8, 7, 8, 5, 27401089600790589603080643761897440542720000000⟩
]

def collectedFourData_9_7_41 : List CollectedFourTerm := [
  ⟨7, 6, 0, 0, 7, 6, -2658904326035601025373210895601250052310302720000000⟩,
  ⟨7, 6, 1, 0, 8, 6, -61190229740514161440769628915593708606324736000000⟩,
  ⟨7, 6, 0, 1, 6, 6, -334520856192998999544140362026149575875624960000000⟩,
  ⟨7, 6, 1, 1, 7, 6, -641683258367879873356937486066655992255348736000000⟩,
  ⟨7, 6, 2, 1, 8, 6, 58809254265814184752781655105191709146873856000000⟩,
  ⟨7, 6, 0, 2, 5, 6, 1617892900069704345245123732019873233145692160000000⟩,
  ⟨7, 6, 1, 2, 6, 6, -760917046313298807468971509057752495065923584000000⟩,
  ⟨7, 6, 2, 2, 7, 6, 71485187463768512162884855630771684525473792000000⟩,
  ⟨7, 6, 3, 2, 8, 6, 4295819196832065402913370624221765183733760000000⟩,
  ⟨7, 6, 0, 3, 4, 6, -1027455272223085444014578180724194773429125120000000⟩,
  ⟨7, 6, 1, 3, 5, 6, -628634867196068304277363757878958029006700544000000⟩,
  ⟨7, 6, 2, 3, 6, 6, 28397697103075939977796119857950279524679680000000⟩,
  ⟨7, 6, 3, 3, 7, 6, 10726185529487721551423858595186626934079488000000⟩,
  ⟨7, 6, 4, 3, 8, 6, 778882688574254927200192135174547274989568000000⟩,
  ⟨7, 6, 0, 4, 3, 6, -3943114023754333888858962716147545310641520640000000⟩,
  ⟨7, 6, 1, 4, 4, 6, 708040511046582582457630149055963528490385408000000⟩,
  ⟨7, 6, 2, 4, 5, 6, 13188436653945975005330428084137375005933568000000⟩,
  ⟨7, 6, 3, 4, 6, 6, 24638182783224178198617707713038656389251072000000⟩,
  ⟨7, 6, 4, 4, 7, 6, 1774906664879778698556502048961332047249408000000⟩,
  ⟨7, 6, 5, 4, 8, 6, -856883889922587664940771855798052291870720000000⟩,
  ⟨7, 6, 0, 5, 2, 6, 6654825875428131862242254409777312014039777280000000⟩,
  ⟨7, 6, 1, 5, 3, 6, 1352176938129237576796595212060950203411202048000000⟩,
  ⟨7, 6, 2, 5, 4, 6, -69928168166028498245856273267702806291152896000000⟩,
  ⟨7, 6, 3, 5, 5, 6, 8097387466026920298674447372308024261607424000000⟩,
  ⟨7, 6, 4, 5, 6, 6, -1628084241385847654001338340483008292716544000000⟩,
  ⟨7, 6, 5, 5, 7, 6, 29149852237477925329023480495929693306880000000⟩,
  ⟨7, 6, 6, 5, 8, 6, -120696987531509114185511661888181238759424000000⟩,
  ⟨7, 6, 0, 6, 1, 6, -4837155557150910010368161575188387255759667200000000⟩,
  ⟨7, 6, 1, 6, 2, 6, -3369514816051574762902744874136421691232878592000000⟩,
  ⟨7, 6, 2, 6, 3, 6, -35284512755037939388005670936280374884433920000000⟩,
  ⟨7, 6, 3, 6, 4, 6, -38203551868556505045968840578148274983141376000000⟩,
  ⟨7, 6, 4, 6, 5, 6, 2641702871578029929160145303431180296650752000000⟩,
  ⟨7, 6, 5, 6, 6, 6, -277267112885473176039739471242953930833920000000⟩,
  ⟨7, 6, 6, 6, 7, 6, -113985842177234979098589854334912766672896000000⟩,
  ⟨7, 6, 7, 6, 8, 6, -11368025491185942152584224895899864662016000000⟩,
  ⟨7, 6, 0, 7, 0, 6, 47178178241530120233731706334168806232487362560000000⟩,
  ⟨7, 6, 1, 7, 1, 6, 9642117836507571043990987364128878646989422592000000⟩,
  ⟨7, 6, 2, 7, 2, 6, 170656845393171215452482659765669803088412672000000⟩,
  ⟨7, 6, 3, 7, 3, 6, 68086660867755141799647569405833509662097408000000⟩,
  ⟨7, 6, 4, 7, 4, 6, 10925061692547697119845432882129990376751104000000⟩,
  ⟨7, 6, 5, 7, 5, 6, 313561476078858302016974282252461245726720000000⟩,
  ⟨7, 6, 6, 7, 6, 6, 123369139247208695959596439042564911267840000000⟩,
  ⟨7, 6, 7, 7, 7, 6, 4017831267661175508654430695033025855488000000⟩,
  ⟨7, 6, 8, 7, 8, 6, 8984014024826132970611226972513317683200000000⟩
]

def collectedFourData_9_7_42 : List CollectedFourTerm := [
  ⟨7, 7, 0, 0, 7, 7, -190506830224444868291288918852714631296502988800000⟩,
  ⟨7, 7, 1, 0, 8, 7, -3653496352622187411176493349768711971746611200000⟩,
  ⟨7, 7, 0, 1, 6, 7, -23967958280136444899814454324920808173364838400000⟩,
  ⟨7, 7, 1, 1, 7, 7, -38313100864753686042657229615212995670127411200000⟩,
  ⟨7, 7, 2, 1, 8, 7, 3009715722895977481274365568775599813138841600000⟩,
  ⟨7, 7, 0, 2, 5, 7, 115919796367576051363230147371233315333236326400000⟩,
  ⟨7, 7, 1, 2, 6, 7, -45432214671242477286159833512692750979222732800000⟩,
  ⟨7, 7, 2, 2, 7, 7, 3658439396143427173622573658716746632344371200000⟩,
  ⟨7, 7, 3, 2, 8, 7, 192368452860524195630599458156522183327744000000⟩,
  ⟨7, 7, 0, 3, 4, 7, -73615754125480830737183613776731143746145484800000⟩,
  ⟨7, 7, 1, 3, 5, 7, -37534018162237907854601319636701436449705164800000⟩,
  ⟨7, 7, 2, 3, 6, 7, 1453325612306706788354485141147477918875648000000⟩,
  ⟨7, 7, 3, 3, 7, 7, 480322755884169100723535545099801295270707200000⟩,
  ⟨7, 7, 4, 3, 8, 7, 31003261728699331171794259198256454461030400000⟩,
  ⟨7, 7, 0, 4, 3, 7, -282518685055137482510574143832470146898303385600000⟩,
  ⟨7, 7, 1, 4, 4, 7, 42275105610605325216129976996426531212990873600000⟩,
  ⟨7, 7, 2, 4, 5, 7, 674952363422037360605169275709999876459724800000⟩,
  ⟨7, 7, 3, 4, 6, 7, 1103307398690998175600307293821509982538956800000⟩,
  ⟨7, 7, 4, 4, 7, 7, 70649786781125149412921789907474267399782400000⟩,
  ⟨7, 7, 5, 4, 8, 7, -30697274840072339695503469753173147018854400000⟩,
  ⟨7, 7, 0, 5, 2, 7, 476809101707578672043436176839063245077820211200000⟩,
  ⟨7, 7, 1, 5, 3, 7, 80734678273059479469996830311405839021873561600000⟩,
  ⟨7, 7, 2, 5, 4, 7, -3578754905670562047484789854517254701029785600000⟩,
  ⟨7, 7, 3, 5, 5, 7, 362604157130380472836534505765795503118745600000⟩,
  ⟨7, 7, 4, 5, 6, 7, -64805551070152206670291049605405399528243200000⟩,
  ⟨7, 7, 5, 5, 7, 7, 1044273367961436588038690830158898239897600000⟩,
  ⟨7, 7, 6, 5, 8, 7, -3930805818827016197718658312499454856396800000⟩,
  ⟨7, 7, 0, 6, 1, 7, -346575528676258205249006921889722763457855488000000⟩,
  ⟨7, 7, 1, 6, 2, 7, -201184243673464069590092610142994871401997926400000⟩,
  ⟨7, 7, 2, 6, 3, 7, -1805776219054919762028810734216474957709312000000⟩,
  ⟨7, 7, 3, 6, 4, 7, -1710769897427389457605491733304580761871974400000⟩,
  ⟨7, 7, 4, 6, 5, 7, 105152427622843710917866259484352913709465600000⟩,
  ⟨7, 7, 5, 6, 6, 7, -9932903242150651450281211835154944124518400000⟩,
  ⟨7, 7, 6, 6, 7, 7, -3712240221216820177642391297727646610227200000⟩,
  ⟨7, 7, 7, 6, 8, 7, -339376399179171488774741406577352874393600000⟩,
  ⟨7, 7, 0, 7, 0, 7, 3380251445887277532451312859845144879995184742400000⟩,
  ⟨7, 7, 1, 7, 1, 7, 575703711141806589252072759063176936262362726400000⟩,
  ⟨7, 7, 2, 7, 2, 7, 8733805541523889578216539731122954173625139200000⟩,
  ⟨7, 7, 3, 7, 3, 7, 3048947130090604725063642859352642148315955200000⟩,
  ⟨7, 7, 4, 7, 4, 7, 434869784660712654835272081700966651605811200000⟩,
  ⟨7, 7, 5, 7, 5, 7, 11233123791510497524748827846631745807974400000⟩,
  ⟨7, 7, 6, 7, 6, 7, 4017831267661175508654430695033025855488000000⟩,
  ⟨7, 7, 7, 7, 7, 7, 119946696916324900162620888488078003404800000⟩,
  ⟨7, 7, 8, 7, 8, 7, 247573931661461199878562339454483169280000000⟩
]

def collectedFourData_9_7_43 : List CollectedFourTerm := [
  ⟨7, 8, 0, 0, 7, 8, -851960134979922316443807045223642856832368640000000⟩,
  ⟨7, 8, 1, 0, 8, 8, -14004596844839853640409536562178944799866880000000⟩,
  ⟨7, 8, 0, 1, 6, 8, -107186419234841871998239688163679863853547520000000⟩,
  ⟨7, 8, 1, 1, 7, 8, -146861931612840130898379838896712492913786880000000⟩,
  ⟨7, 8, 2, 1, 8, 8, 10094747563021883768170106500796598567567360000000⟩,
  ⟨7, 8, 0, 2, 5, 8, 518401598744846170609932290728320145733713920000000⟩,
  ⟨7, 8, 1, 2, 6, 8, -174150947155678117638717317700929490486558720000000⟩,
  ⟨7, 8, 2, 2, 7, 8, 12270601471672124553793232613663357555179520000000⟩,
  ⟨7, 8, 3, 2, 8, 8, 573523629474227122595575033320260291788800000000⟩,
  ⟨7, 8, 0, 3, 4, 8, -329214903987971590906066623460346753911357440000000⟩,
  ⟨7, 8, 1, 3, 5, 8, -143875548678670532567836009971879574524395520000000⟩,
  ⟨7, 8, 2, 3, 6, 8, 4874531860767860461098378666461102918860800000000⟩,
  ⟨7, 8, 3, 3, 7, 8, 1432025086116821324648583028312276142653440000000⟩,
  ⟨7, 8, 4, 3, 8, 8, 83189278881229184208539653770301849731072000000⟩,
  ⟨7, 8, 0, 4, 3, 8, -1263443713647178074313777944601839244337479680000000⟩,
  ⟨7, 8, 1, 4, 4, 8, 162049104065652566239401972919789062602096640000000⟩,
  ⟨7, 8, 2, 4, 5, 8, 2263826338806006033291739655262265493422080000000⟩,
  ⟨7, 8, 3, 4, 6, 8, 3289379595841623165356600950643708248719360000000⟩,
  ⟨7, 8, 4, 4, 7, 8, 189570531864195814679638686030396162834432000000⟩,
  ⟨7, 8, 5, 4, 8, 8, -74880219786112622388364705774449689886720000000⟩,
  ⟨7, 8, 0, 5, 2, 8, 2132324317043409851517284211370374127272591360000000⟩,
  ⟨7, 8, 1, 5, 3, 8, 309472491959805734400775019607859469840547840000000⟩,
  ⟨7, 8, 2, 5, 4, 8, -12003335427277207647638923904119322978549760000000⟩,
  ⟨7, 8, 3, 5, 5, 8, 1081061105225193177765151879939407080325120000000⟩,
  ⟨7, 8, 4, 5, 6, 8, -173889028457806860685604058022658049048576000000⟩,
  ⟨7, 8, 5, 5, 7, 8, 2547308180192589354532291462063592570880000000⟩,
  ⟨7, 8, 6, 5, 8, 8, -8789422017158774444225469129028030955520000000⟩,
  ⟨7, 8, 0, 6, 1, 8, -1549910487954124388682383029218950236235366400000000⟩,
  ⟨7, 8, 1, 6, 2, 8, -771180248245959806767697083710708605371023360000000⟩,
  ⟨7, 8, 2, 6, 3, 8, -6056670052920327815638241424015323509555200000000⟩,
  ⟨7, 8, 3, 6, 4, 8, -5100456681840644369861251364416517969018880000000⟩,
  ⟨7, 8, 4, 6, 5, 8, 282149494562938545440460813142923524702208000000⟩,
  ⟨7, 8, 5, 6, 6, 8, -24229446482184171512793625890910025809920000000⟩,
  ⟨7, 8, 6, 6, 7, 8, -8300701544977886274190411890983782318080000000⟩,
  ⟨7, 8, 7, 6, 8, 8, -700484061820477247638816521840450600960000000⟩,
  ⟨7, 8, 0, 7, 0, 8, 15116725603545715685760063230752929878869278720000000⟩,
  ⟨7, 8, 1, 7, 1, 8, 2206789770251863724793431350673327502246543360000000⟩,
  ⟨7, 8, 2, 7, 2, 8, 29293651069932795632559579756508110724792320000000⟩,
  ⟨7, 8, 3, 7, 3, 8, 9090072712662701241075742274243227853783040000000⟩,
  ⟨7, 8, 4, 7, 4, 8, 1166861219626835899047302453829373123362816000000⟩,
  ⟨7, 8, 5, 7, 5, 8, 27401089600790589603080643761897440542720000000⟩,
  ⟨7, 8, 6, 7, 6, 8, 8984014024826132970611226972513317683200000000⟩,
  ⟨7, 8, 7, 7, 7, 8, 247573931661461199878562339454483169280000000⟩,
  ⟨7, 8, 8, 7, 8, 8, 474500692976227768311657646717403136000000000⟩
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_9_1 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,4}, [645120, -103680, 25920, -10080, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_10_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,8}, [0, -3870720, 0, 725760, -1451520]),
  ({0,1,3,7}, [0, 3870720, 0, -725760, 1451520]),
  ({0,1,4,6}, [0, -1935360, 0, 362880, -725760]),
  ({0,2,3,6}, [0, -1935360, 0, 362880, -725760])
]

def fourHighestCache_10_1 : List (Occupation 24 × List ℚ) := [
  ({0,2,4,5}, [0, 1935360, 0, -362880, 725760]),
  ({1,2,3,5}, [0, 0, 0, 0, 0])
]

def fourHighestCache_10 : List (Occupation 24 × List ℚ) := fourHighestCache_10_0 ++ fourHighestCache_10_1

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate11
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_11_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,9}, [232243200, 46448640, 7257600, -7983360, 2903040, 39916800]),
  ({0,1,3,8}, [-232243200, -46448640, -7257600, 7983360, -2903040, -39916800]),
  ({0,1,4,7}, [348364800, 38707200, 1209600, -3265920, -725760, 39916800]),
  ({0,1,5,6}, [-348364800, -38707200, 4320000, -604800, 3628800, -39916800])
]

def fourHighestCache_11_1 : List (Occupation 24 × List ℚ) := [
  ({0,2,3,7}, [-116121600, 7741440, 6048000, -4717440, 3628800, 0]),
  ({0,2,4,6}, [0, 0, -5529600, 3870720, -2903040, 0]),
  ({0,3,4,5}, [116121600, -7741440, 5011200, -3024000, 2177280, 0]),
  ({1,2,3,6}, [116121600, -7741440, -518400, 846720, -725760, 0])
]

def fourHighestCache_11_2 : List (Occupation 24 × List ℚ) := [
  ({1,2,4,5}, [-116121600, 7741440, 518400, -846720, 725760, 0])
]

def fourHighestCache_11 : List (Occupation 24 × List ℚ) := fourHighestCache_11_0 ++ fourHighestCache_11_1 ++ fourHighestCache_11_2

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate12
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate12. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_12_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,10}, [0, -696729600, -174182400, 65318400, 43545600, -239500800]),
  ({0,1,3,9}, [0, 696729600, 174182400, -65318400, -43545600, 239500800]),
  ({0,1,4,8}, [0, -557383680, -77414400, 29030400, 34836480, -159667200]),
  ({0,1,5,7}, [0, 348364800, 9676800, -3628800, -21772800, 79833600])
]

def fourHighestCache_12_1 : List (Occupation 24 × List ℚ) := [
  ({0,2,3,8}, [0, -139345920, -96768000, 36288000, 8709120, -79833600]),
  ({0,2,4,7}, [0, 209018880, 67737600, -25401600, -13063680, 79833600]),
  ({0,2,5,6}, [0, -348364800, -9676800, 3628800, 21772800, -79833600]),
  ({0,3,4,6}, [0, 69672960, -29030400, 10886400, -4354560, 0])
]

def fourHighestCache_12_2 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,7}, [0, -69672960, 29030400, -10886400, 4354560, 0]),
  ({1,2,4,6}, [0, 69672960, -29030400, 10886400, -4354560, 0]),
  ({1,3,4,5}, [0, -69672960, 29030400, -10886400, 4354560, 0])
]

def fourHighestCache_12 : List (Occupation 24 × List ℚ) := fourHighestCache_12_0 ++ fourHighestCache_12_1 ++ fourHighestCache_12_2

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_13_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,11}, [38320128000, 9580032000, 3353011200, -239500800, -958003200, 1197504000, 6227020800]),
  ({0,1,3,10}, [-38320128000, -9580032000, -3353011200, 239500800, 958003200, -1197504000, -6227020800]),
  ({0,1,4,9}, [61312204800, 9754214400, 1741824000, -174182400, -505128960, 479001600, 6227020800]),
  ({0,1,5,8}, [-61312204800, -9754214400, -503193600, 174182400, 87091200, 159667200, -6227020800])
]

def fourHighestCache_13_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,7}, [68976230400, 8883302400, 43545600, -210470400, 130636800, -479001600, 6227020800]),
  ({0,2,3,9}, [-22992076800, -174182400, 1611187200, -65318400, -452874240, 718502400, 0]),
  ({0,2,4,8}, [0, 0, -1238630400, 0, 418037760, -638668800, 0]),
  ({0,2,5,7}, [-7664025600, 870912000, 459648000, 36288000, -217728000, 319334400, 0])
]

def fourHighestCache_13_2 : List (Occupation 24 × List ℚ) := [
  ({0,3,4,7}, [30656102400, -696729600, 406425600, 29030400, -165473280, 239500800, 0]),
  ({0,3,5,6}, [-22992076800, -174182400, -246758400, -65318400, 174182400, -239500800, 0]),
  ({1,2,3,8}, [22992076800, 174182400, -372556800, 65318400, 34836480, -79833600, 0]),
  ({1,2,4,7}, [-22992076800, -174182400, 372556800, -65318400, -34836480, 79833600, 0])
]

def fourHighestCache_13_3 : List (Occupation 24 × List ℚ) := [
  ({1,2,5,6}, [30656102400, -696729600, -212889600, 29030400, 43545600, -79833600, 0]),
  ({1,3,4,6}, [-7664025600, 870912000, -159667200, 36288000, -8709120, 0, 0]),
  ({2,3,4,5}, [7664025600, -870912000, 159667200, -36288000, 8709120, 0, 0])
]

def fourHighestCache_13 : List (Occupation 24 × List ℚ) := fourHighestCache_13_0 ++ fourHighestCache_13_1 ++ fourHighestCache_13_2 ++ fourHighestCache_13_3

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_14_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,12}, [0, -153280512000, -61312204800, -6706022400, 13412044800, -958003200, -49816166400]),
  ({0,1,3,11}, [0, 153280512000, 61312204800, 6706022400, -13412044800, 958003200, 49816166400]),
  ({0,1,4,10}, [0, -153280512000, -39016857600, -1828915200, 6444748800, 1916006400, -37362124800]),
  ({0,1,5,9}, [0, 122624409600, 22295347200, -2438553600, -696729600, -3832012800, 24908083200])
]

def fourHighestCache_14_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,8}, [0, -61312204800, -11147673600, 2844979200, -1045094400, 2874009600, -12454041600]),
  ({0,2,3,10}, [0, 0, -22295347200, -4877107200, 6967296000, -2874009600, -12454041600]),
  ({0,2,4,9}, [0, 30656102400, 16721510400, 4267468800, -5748019200, 1916006400, 12454041600]),
  ({0,2,5,8}, [0, -61312204800, -11147673600, -406425600, 1741824000, 958003200, -12454041600])
]

def fourHighestCache_14_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,6,7}, [0, 61312204800, 11147673600, -2844979200, 1045094400, -2874009600, 12454041600]),
  ({0,3,4,8}, [0, 0, 0, -3251404800, 2786918400, -1916006400, 0]),
  ({0,3,5,7}, [0, 15328051200, -2786918400, 2946585600, -2177280000, 1437004800, 0]),
  ({0,4,5,6}, [0, -30656102400, 5573836800, -2641766400, 1567641600, -958003200, 0])
]

def fourHighestCache_14_3 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,9}, [0, -30656102400, 5573836800, 609638400, -1219276800, 958003200, 0]),
  ({1,2,4,8}, [0, 30656102400, -5573836800, -609638400, 1219276800, -958003200, 0]),
  ({1,2,5,7}, [0, -15328051200, 2786918400, 304819200, -609638400, 479001600, 0]),
  ({1,3,4,7}, [0, -15328051200, 2786918400, 304819200, -609638400, 479001600, 0])
]

def fourHighestCache_14_4 : List (Occupation 24 × List ℚ) := [
  ({1,3,5,6}, [0, 15328051200, -2786918400, -304819200, 609638400, -479001600, 0]),
  ({2,3,4,6}, [0, 0, 0, 0, 0, 0, 0])
]

def fourHighestCache_14 : List (Occupation 24 × List ℚ) := fourHighestCache_14_0 ++ fourHighestCache_14_1 ++ fourHighestCache_14_2 ++ fourHighestCache_14_3 ++ fourHighestCache_14_4

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_15_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,13}, [8369115955200, 2391175987200, 1120863744000, 261534873600, -149448499200, -112086374400, 373621248000, 1307674368000]),
  ({0,1,3,12}, [-8369115955200, -2391175987200, -1120863744000, -261534873600, 149448499200, 112086374400, -373621248000, -1307674368000]),
  ({0,1,4,11}, [13948526592000, 2759049216000, 795142656000, 114002380800, -74724249600, -76640256000, 211718707200, 1307674368000]),
  ({0,1,5,10}, [-13948526592000, -2759049216000, -516450816000, 3048192000, 18289152000, 38320128000, -62270208000, -1307674368000])
]

def fourHighestCache_15_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,9}, [16738231910400, 2575112601600, 276950016000, -32920473600, -4702924800, -2874009600, -37362124800, 1307674368000]),
  ({0,1,7,8}, [-16738231910400, -2575112601600, -109734912000, 19914854400, 10973491200, -20118067200, 87178291200, -1307674368000]),
  ({0,2,3,11}, [-5579410636800, -367873228800, 325721088000, 147532492800, -74724249600, -35446118400, 161902540800, 0]),
  ({0,2,4,10}, [0, 0, -278691840000, -117050572800, 56435097600, 38320128000, -149448499200, 0])
]

def fourHighestCache_15_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,5,9}, [-2789705318400, 183936614400, 239500800000, 29872281600, -13586227200, -35446118400, 99632332800, 0]),
  ({0,2,6,8}, [0, 0, -167215104000, 13005619200, -6270566400, 22992076800, -49816166400, 0]),
  ({0,3,4,9}, [8369115955200, 183936614400, -7838208000, 56696371200, -24559718400, -5748019200, 37362124800, 0]),
  ({0,3,5,8}, [-5579410636800, -367873228800, -8709120000, -34546176000, 13063680000, 10538035200, -37362124800, 0])
]

def fourHighestCache_15_3 : List (Occupation 24 × List ℚ) := [
  ({0,3,6,7}, [8369115955200, 183936614400, 75769344000, -1828915200, 3657830400, -17244057600, 37362124800, 0]),
  ({0,4,5,7}, [-2789705318400, 183936614400, -39191040000, 16866662400, -7315660800, 2874009600, 0, 0]),
  ({1,2,3,10}, [5579410636800, 367873228800, -47029248000, -30481920000, 18289152000, -2874009600, -12454041600, 0]),
  ({1,2,4,9}, [-5579410636800, -367873228800, 47029248000, 30481920000, -18289152000, 2874009600, 12454041600, 0])
]

def fourHighestCache_15_4 : List (Occupation 24 × List ℚ) := [
  ({1,2,5,8}, [8369115955200, 183936614400, -63576576000, -8331724800, 6793113600, 1916006400, -12454041600, 0]),
  ({1,2,6,7}, [-8369115955200, -183936614400, 91445760000, -11176704000, 2612736000, -5748019200, 12454041600, 0]),
  ({1,3,4,8}, [-2789705318400, 183936614400, 16547328000, -22150195200, 11496038400, -4790016000, 0, 0]),
  ({1,3,5,7}, [0, 0, -27869184000, 19508428800, -9405849600, 3832012800, 0, 0])
]

def fourHighestCache_15_5 : List (Occupation 24 × List ℚ) := [
  ({1,4,5,6}, [2789705318400, -183936614400, 39191040000, -16866662400, 7315660800, -2874009600, 0, 0]),
  ({2,3,4,7}, [2789705318400, -183936614400, 11321856000, 2641766400, -2090188800, 958003200, 0, 0]),
  ({2,3,5,6}, [-2789705318400, 183936614400, -11321856000, -2641766400, 2090188800, -958003200, 0, 0])
]

def fourHighestCache_15 : List (Occupation 24 × List ℚ) := fourHighestCache_15_0 ++ fourHighestCache_15_1 ++ fourHighestCache_15_2 ++ fourHighestCache_15_3 ++ fourHighestCache_15_4 ++ fourHighestCache_15_5

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate16
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate16. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_16_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,14}, [0, -41845579776000, -20922789888000, -6799906713600, 1046139494400, 2615348736000, -2092278988800, -13076743680000]),
  ({0,1,3,13}, [0, 41845579776000, 20922789888000, 6799906713600, -1046139494400, -2615348736000, 2092278988800, 13076743680000]),
  ({0,1,4,12}, [0, -47823519744000, -16554295296000, -3540779827200, 643778150400, 1437004800000, -747242496000, -10461394944000]),
  ({0,1,5,11}, [0, 41845579776000, 12339081216000, 1005903360000, -402361344000, -383201280000, -373621248000, 7846046208000])
]

def fourHighestCache_16_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,10}, [0, -29889699840000, -7587385344000, -91445760000, 329204736000, -143700480000, 747242496000, -5230697472000]),
  ({0,1,7,9}, [0, 16738231910400, 3218890752000, -7315660800, -219469824000, 201180672000, -523069747200, 2615348736000]),
  ({0,2,3,12}, [0, 5977939968000, -4368494592000, -3259126886400, 402361344000, 1178343936000, -1345036492800, -2615348736000]),
  ({0,2,4,11}, [0, 5977939968000, 4215214080000, 2534876467200, -241416806400, -1053803520000, 1120863744000, 2615348736000])
]

def fourHighestCache_16_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,5,10}, [0, -11955879936000, -4751695872000, -914457600000, 73156608000, 526901760000, -373621248000, -2615348736000]),
  ({0,2,6,9}, [0, 13151467929600, 4368494592000, 98761420800, -109734912000, -57480192000, -224172748800, 2615348736000]),
  ({0,2,7,8}, [0, -16738231910400, -3218890752000, 7315660800, 219469824000, -201180672000, 523069747200, -2615348736000]),
  ({0,3,4,10}, [0, -5977939968000, 689762304000, -896168448000, 7315660800, 402361344000, -523069747200, 0])
]

def fourHighestCache_16_3 : List (Occupation 24 × List ℚ) := [
  ({0,3,5,9}, [0, 8369115955200, -229920768000, 493807104000, 95103590400, -373621248000, 448345497600, 0]),
  ({0,3,6,8}, [0, -2391175987200, -459841536000, -65840947200, -102419251200, 201180672000, -224172748800, 0]),
  ({0,4,5,8}, [0, -9564703948800, 613122048000, -146313216000, -58525286400, 134120448000, -149448499200, 0]),
  ({0,4,6,7}, [0, 8369115955200, -229920768000, 25604812800, 95103590400, -143700480000, 149448499200, 0])
]

def fourHighestCache_16_4 : List (Occupation 24 × List ℚ) := [
  ({1,2,3,11}, [0, -11955879936000, 153280512000, 724250419200, -160944537600, -124540416000, 224172748800, 0]),
  ({1,2,4,10}, [0, 11955879936000, -153280512000, -724250419200, 160944537600, 124540416000, -224172748800, 0]),
  ({1,2,5,9}, [0, -9564703948800, 613122048000, 321889075200, -58525286400, -95800320000, 149448499200, 0]),
  ({1,2,6,8}, [0, 5977939968000, -689762304000, -40236134400, -7315660800, 57480192000, -74724249600, 0])
]

def fourHighestCache_16_5 : List (Occupation 24 × List ℚ) := [
  ({1,3,4,9}, [0, -2391175987200, -459841536000, 402361344000, -102419251200, -28740096000, 74724249600, 0]),
  ({1,3,5,8}, [0, 3586763980800, 76640256000, -281652940800, 65840947200, 38320128000, -74724249600, 0]),
  ({1,3,6,7}, [0, -5977939968000, 689762304000, 40236134400, 7315660800, -57480192000, 74724249600, 0]),
  ({1,4,5,7}, [0, 1195587993600, -383201280000, 120708403200, -36578304000, 9580032000, 0, 0])
]

def fourHighestCache_16_6 : List (Occupation 24 × List ℚ) := [
  ({2,3,4,8}, [0, -1195587993600, 383201280000, -120708403200, 36578304000, -9580032000, 0, 0]),
  ({2,3,5,7}, [0, 1195587993600, -383201280000, 120708403200, -36578304000, 9580032000, 0, 0]),
  ({2,4,5,6}, [0, -1195587993600, 383201280000, -120708403200, 36578304000, -9580032000, 0, 0])
]

def fourHighestCache_16 : List (Occupation 24 × List ℚ) := fourHighestCache_16_0 ++ fourHighestCache_16_1 ++ fourHighestCache_16_2 ++ fourHighestCache_16_3 ++ fourHighestCache_16_4 ++ fourHighestCache_16_5 ++ fourHighestCache_16_6

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate17
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_17_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,15}, [2343352467456000, 732297646080000, 402763705344000, 159536272896000, 10461394944000, -44460928512000, -5230697472000, 128152088064000, 355687428096000]),
  ({0,1,3,14}, [-2343352467456000, -732297646080000, -402763705344000, -159536272896000, -10461394944000, 44460928512000, 5230697472000, -128152088064000, -355687428096000]),
  ({0,1,4,13}, [4017175658496000, 920602755072000, 343731548160000, 94152554496000, 2092278988800, -23164517376000, -8518564454400, 83691159552000, 355687428096000]),
  ({0,1,5,12}, [-4017175658496000, -920602755072000, -270156902400000, -42650302464000, 5633058816000, 5460618240000, 9714152448000, -41845579776000, -355687428096000])
]

def fourHighestCache_17_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,11}, [5021469573120000, 899679965184000, 176981511168000, 16295634432000, -7242504192000, 1293304320000, -5977939968000, 10461394944000, 355687428096000]),
  ({0,1,7,10}, [-5021469573120000, -899679965184000, -103406865408000, -2249565696000, 3730987008000, -603542016000, 0, 10461394944000, -355687428096000]),
  ({0,1,8,9}, [5356234211328000, 870388059340800, 70815596544000, -5559902208000, 58525286400, -1609445376000, 4184557977600, -20922789888000, 355687428096000]),
  ({0,2,3,13}, [-1673823191040000, -188305108992000, 59032157184000, 65383718400000, 8369115955200, -21296411136000, 3287866982400, 44460928512000, 0])
]

def fourHighestCache_17_2 : List (Occupation 24 × List ℚ) := [
  ({0,2,4,12}, [0, 0, -73574645760000, -51502252032000, -7725337804800, 17703899136000, -1195587993600, -41845579776000, 0]),
  ({0,2,5,11}, [-1004293914624000, 20922789888000, 93175391232000, 26354668032000, 1609445376000, -6753922560000, -3736212480000, 31384184832000, 0]),
  ({0,2,6,10}, [0, 0, -73574645760000, -14046068736000, 3511517184000, -689762304000, 5977939968000, -20922789888000, 0]),
  ({0,2,7,9}, [-334764638208000, 29291905843200, 32591268864000, 7809467904000, -3789512294400, 2212987392000, -4184557977600, 10461394944000, 0])
]

def fourHighestCache_17_3 : List (Occupation 24 × List ℚ) := [
  ({0,3,4,11}, [2678117105664000, 167382319104000, -5058256896000, 11266117632000, 5472114278400, -7357464576000, 2839521484800, 7846046208000, 0]),
  ({0,3,5,10}, [-1673823191040000, -188305108992000, -14542488576000, -4846625280000, -4974649344000, 5604318720000, -1494484992000, -7846046208000, 0]),
  ({0,3,6,9}, [3012881743872000, 138090413260800, 21210190848000, 3456649728000, 833985331200, -1293304320000, -1345036492800, 7846046208000, 0]),
  ({0,3,7,8}, [-2678117105664000, -167382319104000, -9656672256000, -6584094720000, 2721425817600, -1609445376000, 3138418483200, -7846046208000, 0])
]

def fourHighestCache_17_4 : List (Occupation 24 × List ℚ) := [
  ({0,4,5,9}, [-1339058552832000, 50214695731200, 8047226880000, -3292047360000, 3438360576000, -2701569024000, 1643933491200, 0, 0]),
  ({0,4,6,8}, [0, 0, -14714929152000, 4682022912000, -3043314892800, 2069286912000, -1195587993600, 0, 0]),
  ({0,5,6,7}, [1004293914624000, -20922789888000, 17186577408000, -5285564928000, 2487324672000, -1408264704000, 747242496000, 0, 0]),
  ({1,2,3,12}, [1673823191040000, 188305108992000, 14542488576000, -13881466368000, -643778150400, 3592512000000, -2092278988800, -2615348736000, 0])
]

def fourHighestCache_17_8 : List (Occupation 24 × List ℚ) := [
  ({2,4,5,7}, [-334764638208000, 29291905843200, -4196054016000, 786433536000, -160944537600, 28740096000, 0, 0, 0]),
  ({3,4,5,6}, [334764638208000, -29291905843200, 4196054016000, -786433536000, 160944537600, -28740096000, 0, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Highest. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def firstFourCopy {D : ℕ} (hD : 1 ≤ D) : CopyLabel D := ⟨⟨1,by omega⟩, by change Odd (1:ℕ); decide⟩



end LaughlinFock
end

end OAI
end


