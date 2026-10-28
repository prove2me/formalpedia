-- Prove2me | Definitions.Def_OAIQ084L000
-- name    : OAIQ084L000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:22:05.196181+00:00
-- url     : https://prove2.me/theorems/a2fd9d6f-2316-484c-af84-0bc82e70cf70
-- title:
--   Definitions bundle OAIQ084L000 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 378 declarations of OpenAI's Lean: 335 definitions, 4 inductive types or structures, 4 instances and 35 theorems. The definitions and types are `OAI.LaughlinFock.AnnihilationSpace`, `OAI.LaughlinFock.BodySpace`, `OAI.LaughlinFock.CollectedFourTerm`, `OAI.LaughlinFock.ComparedThreeBlock`, `OAI.LaughlinFock.ComparisonRow`, `OAI.LaughlinFock.CopyLabel`, `OAI.LaughlinFock.CoupledIndex`, `OAI.LaughlinFock.CubeLayer`, `OAI.LaughlinFock.CubeVector`, `OAI.LaughlinFock.FockRotationIndex`, `OAI.LaughlinFock.FockRotationSpace`, `OAI.LaughlinFock.FourHighestShell`, `OAI.LaughlinFock.FourSpinIndex`, `OAI.LaughlinFock.FourUncoupled`, `OAI.LaughlinFock.GridLayer`, `OAI.LaughlinFock.GridSupported`, `OAI.LaughlinFock.GridVector`, `OAI.LaughlinFock.IncreasingPair`, `OAI.LaughlinFock.NumericRowEntry`, `OAI.LaughlinFock.PairLabel`, `OAI.LaughlinFock.RowEntry`, `OAI.LaughlinFock.SectorOccupation`, `OAI.LaughlinFock.UnitaryFamily`, `OAI.LaughlinFock.ValidFourCopy`, `OAI.LaughlinFock.annihilatorList`, `OAI.LaughlinFock.annihilatorVector`, `OAI.LaughlinFock.auxiliaryRow`, `OAI.LaughlinFock.averagedFourComparison`, `OAI.LaughlinFock.averagedOperatorsContinuousENorm`, `OAI.LaughlinFock.averagedRowsFour`, `OAI.LaughlinFock.averagingContinuousENorm`, `OAI.LaughlinFock.averagingRotationMeasurableSpace`, `OAI.LaughlinFock.basisAnnihilator`, `OAI.LaughlinFock.boundedEntriesDecidable`, `OAI.LaughlinFock.boundedMatrixEntriesDecidable`, `OAI.LaughlinFock.cachedFourGram`, `OAI.LaughlinFock.certificateAlpha`, `OAI.LaughlinFock.certificateAlphaData`, `OAI.LaughlinFock.certificateEll`, `OAI.LaughlinFock.certificateEllData` and 299 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinFock_AllowanceOrbit`, `LaughlinFock_AveragedOperators`, `LaughlinFock_Averaging`, `LaughlinFock_BesselComparison`, `LaughlinFock_CertificateRows`, `LaughlinFock_Covariance`, `LaughlinFock_CreationRows`, `LaughlinFock_FastWedge`, `LaughlinFock_FermionOperators`, `LaughlinFock_FiniteComparison`, `LaughlinFock_FiniteCoupling`, `LaughlinFock_FockRotations`, `LaughlinFock_FourCoefficients`, `LaughlinFock_FourCopies`, `LaughlinFock_GramCache`, `LaughlinFock_LadderCalculus`, `LaughlinFock_Model`, `LaughlinFock_NormalOrdering`, `LaughlinFock_NumericTrace`, `LaughlinFock_PartsTrace`, `LaughlinFock_RationalThree`, `LaughlinFock_RationalWedge`, `LaughlinFock_RelativePerturbation`, `LaughlinFock_RelativeTransfer`, `LaughlinFock_Rotations`, `LaughlinFock_RowTraces`, `LaughlinFock_Sparse1001`, `LaughlinFock_Sparse1002`, `LaughlinFock_Sparse1003`, `LaughlinFock_Sparse1004`, `LaughlinFock_Sparse1005`, `LaughlinFock_Sparse1006`, `LaughlinFock_Sparse1007`, `LaughlinFock_Sparse1008`, `LaughlinFock_Sparse1009`, `LaughlinFock_Sparse1010`, `LaughlinFock_Sparse1011`, `LaughlinFock_Sparse1012`, `LaughlinFock_Sparse1013`, `LaughlinFock_Sparse1014`, `LaughlinFock_Sparse1101`, `LaughlinFock_Sparse1103`, `LaughlinFock_Sparse1105`, `LaughlinFock_Sparse1106`, `LaughlinFock_SparseTrace`, `LaughlinFock_SphereScaling`, `LaughlinFock_SpinSchur`, `LaughlinFock_SwapCompression`, `LaughlinFock_TensorBasis`, `LaughlinFock_ThreeRows`, `LaughlinFock_ThreeTraces`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ084L002`, `OAIQ084L003`, `OAIQ084L004`, `OAIQ084L005`, `OAIQ084L006`, `OAIQ084L007`, `OAIQ084L008`, `OAIQ084L009`, `OAIQ084L010`, `OAIQ084L011`, `OAIQ084L012`, `OAIQ084L013`, `OAIQ084L014`, `OAIQ084L015`, `OAIQ084L016`, `OAIQ084L017`, `OAIQ084L018`, `OAIQ084L019`, `OAIQ084L020` and `OAIQ084L021`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model. -/
noncomputable section

namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder


abbrev SectorOccupation (Q n : ℕ) := {A : Occupation Q // A.card = n}


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FermionOperators
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
def fermionSign {Q : ℕ} (j : Orbital Q) (B : Occupation Q) : ℂ :=
  (-1 : ℂ) ^ (B.filter (fun i => i < j)).card

@[simp] theorem fermionSign_star {Q : ℕ} (j : Orbital Q) (B : Occupation Q) :
    star (fermionSign j B) = fermionSign j B := by simp [fermionSign]

@[simp] theorem fermionSign_mul_self {Q : ℕ} (j : Orbital Q) (B : Occupation Q) :
    fermionSign j B * fermionSign j B = 1 := by
  unfold fermionSign
  rw [← mul_pow]
  simp

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SphereScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sphere Scaling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
def occupationDiagonal (Q : ℕ) (d : Orbital Q → ℂ) : FockMatrix Q :=
  Matrix.diagonal (fun A => ∏ j ∈ A, d j)

 
def occupationDiagonalInv (Q : ℕ) (d : Orbital Q → ℂ) : FockMatrix Q :=
  Matrix.diagonal (fun A => (∏ j ∈ A, d j)⁻¹)


def diagonalConjugate (Q : ℕ) (d : Orbital Q → ℂ) (A : FockMatrix Q) : FockMatrix Q :=
  occupationDiagonalInv Q d * A * occupationDiagonal Q d

@[simp] theorem diagonalConjugate_zero (Q : ℕ) (d : Orbital Q → ℂ) :
    diagonalConjugate Q d 0 = 0 := by simp [diagonalConjugate]

 
def coefficientPairAnnihilator (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) : FockMatrix Q :=
  ∑ i : Orbital Q, ∑ j : Orbital Q,
    if i < j then a i j • (annihilator Q j * annihilator Q i) else 0

open Filter Topology


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativePerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Perturbation. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker

 
def stackFamily {β ι κ : Type*} (A : β → Matrix ι κ ℂ) : Matrix (β × ι) κ ℂ :=
  fun b j => A b.1 b.2 j

@[simp]
theorem stackFamily_mulVec {β ι κ : Type*} [Fintype κ]
    (A : β → Matrix ι κ ℂ) (x : κ → ℂ) (b : β) (i : ι) :
    (stackFamily A *ᵥ x) (b,i) = (A b *ᵥ x) i := rfl


def orbitalMerge (L R : ℕ) : Orbital L ⊕ Fin R ≃ Orbital (L+R) :=
  finSumFinEquiv.trans (finCongr (by omega))

def localOrbital (L R : ℕ) (j : Orbital L) : Orbital (L+R) :=
  orbitalMerge L R (Sum.inl j)

def spectatorOrbital (L R : ℕ) (j : Fin R) : Orbital (L+R) :=
  orbitalMerge L R (Sum.inr j)

@[simp] theorem localOrbital_val (L R : ℕ) (j : Orbital L) :
    (localOrbital L R j).val = j.val := rfl

@[simp] theorem spectatorOrbital_val (L R : ℕ) (j : Fin R) :
    (spectatorOrbital L R j).val = L+1+j.val := rfl

 

def occupationMerge (L R : ℕ) : Occupation L × Finset (Fin R) ≃ Occupation (L+R) :=
  Finset.sumEquiv.toEquiv.symm.trans (orbitalMerge L R).finsetCongr


def spectatorExtension (L R : ℕ) (M : FockMatrix L) : FockMatrix (L+R) :=
  (M ⊗ₖ (1 : Matrix (Finset (Fin R)) (Finset (Fin R)) ℂ)).submatrix
    (occupationMerge L R).symm (occupationMerge L R).symm

@[simp] theorem spectatorExtension_zero (L R : ℕ) :
    spectatorExtension L R 0 = 0 := by
  simp only [spectatorExtension, Matrix.zero_kronecker, Matrix.submatrix_zero,
    Pi.zero_apply]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NormalOrdering
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

 

def annihilatorList (Q : ℕ) : List (Orbital Q) → FockMatrix Q
  | [] => 1
  | j :: js => annihilatorList Q js * annihilator Q j

@[simp] theorem annihilatorList_nil (Q : ℕ) : annihilatorList Q [] = 1 := rfl

@[simp] theorem annihilatorList_cons (Q : ℕ) (j : Orbital Q) (js : List (Orbital Q)) :
    annihilatorList Q (j :: js) = annihilatorList Q js * annihilator Q j := rfl

 
def basisAnnihilator (Q : ℕ) (A : Occupation Q) : FockMatrix Q :=
  annihilatorList Q (A.sort (· ≤ ·))


def exteriorLift (Q k : ℕ) (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    FockMatrix Q :=
  ∑ A, ∑ B, M A B • ((basisAnnihilator Q A.val)ᴴ * basisAnnihilator Q B.val)



def AnnihilationSpace (Q k : ℕ) : Submodule ℂ (FockMatrix Q) :=
  Submodule.span ℂ (Set.range (fun S : SectorOccupation Q k => basisAnnihilator Q S.val))



def annihilatorVector (Q k : ℕ) (M : FockMatrix Q) : SectorOccupation Q k → ℂ :=
  fun S => star (M ∅ S.val)


def exteriorLiftLinear (Q k : ℕ) :
    Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ →ₗ[ℂ] FockMatrix Q where
  toFun := exteriorLift Q k
  map_add' M N := by
    simp only [exteriorLift, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [exteriorLift, Matrix.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, RingHom.id_apply]

@[simp] theorem exteriorLift_add (Q k : ℕ)
    (M N : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    exteriorLift Q k (M+N) = exteriorLift Q k M + exteriorLift Q k N :=
  (exteriorLiftLinear Q k).map_add M N

@[simp] theorem exteriorLift_sub (Q k : ℕ)
    (M N : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    exteriorLift Q k (M-N) = exteriorLift Q k M - exteriorLift Q k N :=
  (exteriorLiftLinear Q k).map_sub M N

@[simp] theorem exteriorLift_sum {α : Type*} (Q k : ℕ) (s : Finset α)
    (M : α → Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    exteriorLift Q k (∑ a ∈ s, M a) = ∑ a ∈ s, exteriorLift Q k (M a) :=
  map_sum (exteriorLiftLinear Q k) M s

 

def BodySpace (Q k : ℕ) : Submodule ℂ (FockMatrix Q) :=
  LinearMap.range (exteriorLiftLinear Q k)


abbrev IncreasingPair (Q : ℕ) := {ij : Orbital Q × Orbital Q // ij.1 < ij.2}

theorem sort_pair {Q : ℕ} (i j : Orbital Q) (hij : i<j) :
    ( {i,j} : Occupation Q).sort (· ≤ ·) = [i,j] := by
  have hd : ([i,j] : List (Orbital Q)).Nodup := by simp [ne_of_lt hij]
  have hs : ([i,j] : List (Orbital Q)).Pairwise (· ≤ ·) := by simp [hij.le]
  simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty] using
    (List.toFinset_sort (r := (· ≤ ·)) hd).mpr hs

def increasingPairSector (Q : ℕ) (ij : IncreasingPair Q) : SectorOccupation Q 2 :=
  ⟨{ij.val.1,ij.val.2}, by simp [ne_of_lt ij.property]⟩

theorem increasingPairSector_injective (Q : ℕ) : Function.Injective (increasingPairSector Q) := by
  intro ij kl h
  have hs := congrArg (fun S : SectorOccupation Q 2 => S.val.sort (· ≤ ·)) h
  simp only [increasingPairSector, sort_pair _ _ ij.property, sort_pair _ _ kl.property,
    List.cons.injEq, and_true] at hs
  exact Subtype.ext (Prod.ext hs.1 hs.2)

theorem increasingPairSector_surjective (Q : ℕ) : Function.Surjective (increasingPairSector Q) := by
  intro S
  have hlen : (S.val.sort (· ≤ ·)).length = 2 := by rw [Finset.length_sort, S.property]
  obtain ⟨i,j,hij⟩ := List.length_eq_two.mp hlen
  have hlt : i<j := by
    have hs := S.val.sortedLT_sort
    rw [hij] at hs
    simpa using hs.pairwise
  refine ⟨⟨(i,j),hlt⟩,?_⟩
  apply Subtype.ext
  have h := Finset.sort_toFinset S.val (· ≤ ·)
  rw [hij] at h
  simpa only [increasingPairSector, List.toFinset_cons, List.toFinset_nil,
    Finset.insert_empty] using h

def increasingPairEquiv (Q : ℕ) : IncreasingPair Q ≃ SectorOccupation Q 2 :=
  Equiv.ofBijective (increasingPairSector Q)
    ⟨increasingPairSector_injective Q, increasingPairSector_surjective Q⟩

@[simp] theorem increasingPairEquiv_apply (Q : ℕ) (ij : IncreasingPair Q) :
    increasingPairEquiv Q ij = increasingPairSector Q ij := rfl

abbrev PairLabel (Q : ℕ) := Fin (2*Q-1)


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteCoupling
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

 

def highestWeight (n m z p : ℕ) : ℕ :=
  z.choose p * (n-p).descFactorial (z-p) * (m-z+p).descFactorial p

def highestTotal (n m z : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (z+1), highestWeight n m z p

 
def highestCoefficient (n m z p : ℕ) : ℝ :=
  (-1)^(z-p) * Real.sqrt ((highestWeight n m z p : ℝ) / highestTotal n m z)



def coupledCoefficient (n m z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => highestCoefficient n m z p
  | k+1, p =>
      ((if p = 0 then 0 else
         Real.sqrt ((p : ℝ)*((n : ℝ)+1-p)) * coupledCoefficient n m z k (p-1)) +
       Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) *
         Real.sqrt ((m : ℝ)+p-z-k) * coupledCoefficient n m z k p) /
        Real.sqrt (((k+1 : ℕ) : ℝ)*((n : ℝ)+m-2*z-k))



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCoefficients
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



def sphericalCopyCoefficient (Q D T r p j k : ℕ) : ℝ :=
  if Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ j+k ∧ p+j+k = T then
    Real.sqrt 2 * coupledCoefficient Q Q r (j+k-r) j *
      coupledCoefficient (2*Q-2) (2*Q-2*r) (D-r) (T-D) p
  else 0



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

 

def spinStep (n p : ℕ) : ℝ := Real.sqrt ((p : ℝ) * ((n : ℝ)+1-p))

@[simp] theorem spinStep_zero (n : ℕ) : spinStep n 0 = 0 := by simp [spinStep]

theorem spinStep_cutoff (n p : ℕ) (hp : n < p) : spinStep n p = 0 := by
  apply Real.sqrt_eq_zero_of_nonpos
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p)
  have h : (n : ℝ)+1 ≤ p := by exact_mod_cast hp
  linarith

@[simp] theorem spinStep_last (n : ℕ) : spinStep n (n+1) = 0 :=
  spinStep_cutoff n (n+1) (by omega)

abbrev GridVector := ℕ → ℕ → ℝ

def GridSupported (n m : ℕ) (f : GridVector) : Prop :=
  ∀ p q, n < p ∨ m < q → f p q = 0

def GridLayer (T : ℕ) (f : GridVector) : Prop :=
  ∀ p q, p+q ≠ T → f p q = 0


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TensorBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators



abbrev CoupledIndex (n m : ℕ) :=
  (z : Fin (min n m + 1)) × Fin (n+m-2*z.val+1)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_BesselComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bessel Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
abbrev CopyLabel (D : ℕ) := {r : Fin (D+1) // Odd r.val}

 
abbrev FourUncoupled (Q : ℕ) := Fin (2*Q-2+1) × IncreasingPair Q

 
abbrev FourHighestShell (Q D : ℕ) :=
  {b : FourUncoupled Q // b.1.val+b.2.val.1.val+b.2.val.2.val=D}



def highestCopyMatrix (Q D : ℕ) : Matrix (CopyLabel D) (FourHighestShell Q D) ℂ :=
  fun r b => sphericalCopyCoefficient Q D D r.val.val
    b.val.1.val b.val.2.val.1.val b.val.2.val.2.val



def shellFourAnnihilator (Q D : ℕ) (b : FourHighestShell Q D) : FockMatrix Q :=
  annihilator Q b.val.2.val.2 * annihilator Q b.val.2.val.1 * pairAnnihilator Q b.val.1.val

 

def highestFourAnnihilator (Q D : ℕ) (r : CopyLabel D) : FockMatrix Q :=
  ∑ b : FourHighestShell Q D, highestCopyMatrix Q D r b • shellFourAnnihilator Q D b



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CreationRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation Rows. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder Kronecker BigOperators



def auxiliaryRow {β : Type*} [Fintype β] (Q t : ℕ) (ℓ : ℝ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) : FockMatrix Q :=
  ℓ • pairAnnihilator Q t + ∑ b, a b •
    ((annihilator Q (i b))ᴴ * (annihilator Q (j b) * pairAnnihilator Q (p b)))


def rowFourBody {β : Type*} [Fintype β] (Q : ℕ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) : FockMatrix Q :=
  -(∑ b, ∑ c, (a b*a c) •
    (annihilator Q (i c) * (annihilator Q (j b) * pairAnnihilator Q (p b)))ᴴ *
      (annihilator Q (i b) * (annihilator Q (j c) * pairAnnihilator Q (p c))))



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

abbrev CubeVector := ℕ → ℕ → ℕ → ℝ

def CubeLayer (T : ℕ) (f : CubeVector) : Prop :=
  ∀ i j k, i+j+k ≠ T → f i j k = 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_AveragedOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaged Operators. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder BigOperators
open MeasureTheory
local instance averagedOperatorsContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))



def matrixConjugationAverage {G ι : Type*} [MeasurableSpace G] [Fintype ι]
    (μ : Measure G) (U : G → Matrix ι ι ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ g, U g * M * (U g)ᴴ ∂μ

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Covariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

def oneBodyLift (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) : FockMatrix Q :=
  ∑ i, ∑ j, A i j • ((annihilator Q i)ᴴ * annihilator Q j)

theorem oneBodyLift_add (Q : ℕ) (A B : Matrix (Orbital Q) (Orbital Q) ℂ) :
    oneBodyLift Q (A+B) = oneBodyLift Q A + oneBodyLift Q B := by
  simp [oneBodyLift, add_smul, Finset.sum_add_distrib]

theorem oneBodyLift_smul (Q : ℕ) (c : ℂ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    oneBodyLift Q (c • A) = c • oneBodyLift Q A := by
  simp [oneBodyLift, smul_smul, Finset.smul_sum]

def oneBodyLiftLinear (Q : ℕ) :
    Matrix (Orbital Q) (Orbital Q) ℂ →ₗ[ℂ] FockMatrix Q where
  toFun := oneBodyLift Q
  map_add' := oneBodyLift_add Q
  map_smul' := oneBodyLift_smul Q

theorem oneBodyLift_adjoint (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    (oneBodyLift Q A)ᴴ = oneBodyLift Q Aᴴ := by
  simp only [oneBodyLift, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]


def sectorOneBody (Q k : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ :=
  (oneBodyLift Q A).submatrix Subtype.val Subtype.val

theorem sectorOneBody_adjoint (Q k : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    (sectorOneBody Q k A)ᴴ = sectorOneBody Q k Aᴴ := by
  rw [sectorOneBody, Matrix.conjTranspose_submatrix, oneBodyLift_adjoint]
  rfl



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Rotations
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

theorem matrix_unitary_isClosed {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) :=
  isClosed_unitary

section UnitaryCompact
open scoped Matrix.Norms.Elementwise

 
theorem unitaryMatrix_compactSpace {ι : Type*} [Fintype ι] [DecidableEq ι] :
    CompactSpace (Matrix.unitaryGroup ι ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Matrix ι ι ℂ) 1).of_isClosed_subset
    matrix_unitary_isClosed
  intro U hU
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact entrywise_sup_norm_bound_of_unitary hU

end UnitaryCompact


section Simultaneous
variable {J : Type*} (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]

 

abbrev UnitaryFamily := ∀ j, Matrix.unitaryGroup (I j) ℂ



end Simultaneous

section Flows
open scoped Matrix.Norms.Operator
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]

 
theorem rotation_exp_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) (t : ℝ) :
    exp ((t : ℂ) • A) ∈ Matrix.unitaryGroup ι ℂ := by
  let B : Matrix ι ι ℂ := (t : ℂ) • A
  have hB : Bᴴ = -B := by
    dsimp only [B]
    rw [Matrix.conjTranspose_smul, hA]
    simp
  have hstar : (exp B)ᴴ = exp (-B) := by
    rw [← Matrix.exp_conjTranspose, hB]
  change (exp B) ∈ unitary (Matrix ι ι ℂ)
  rw [Unitary.mem_iff]
  change (exp B)ᴴ * exp B = 1 ∧ exp B * (exp B)ᴴ = 1
  rw [hstar]
  constructor
  · simpa only [neg_add_cancel, exp_zero] using!
      (exp_add_of_commute (Commute.refl B).neg_left).symm
  · simpa only [add_neg_cancel, exp_zero] using!
      (exp_add_of_commute (Commute.refl B).neg_right).symm

def rotationFlow (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) (s : σ) (t : ℝ) : UnitaryFamily I :=
  fun j => ⟨exp ((t : ℂ) • X s j), rotation_exp_unitary (X s j) (hX s j) t⟩



def rotationGroup (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) : Subgroup (UnitaryFamily I) :=
  (Subgroup.closure (Set.range (fun p : σ × ℝ => rotationFlow X hX p.1 p.2))).topologicalClosure

instance rotationGroup_compactSpace (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
    (hX : ∀ s j, (X s j)ᴴ = -X s j) : CompactSpace (rotationGroup X hX) := by
  let (j : J) : CompactSpace (Matrix.unitaryGroup (I j) ℂ) := unitaryMatrix_compactSpace
  apply isCompact_iff_compactSpace.mp
  exact (Subgroup.isClosed_topologicalClosure _).isCompact

end Flows
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open NormedSpace MeasureTheory Topology
local instance averagingContinuousENorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    ContinuousENorm (Matrix ι κ ℂ) :=
  inferInstanceAs (ContinuousENorm (ι → κ → ℂ))

section
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
  (hX : ∀ s j, (X s j)ᴴ = -X s j)

local instance averagingRotationMeasurableSpace : MeasurableSpace (rotationGroup X hX) := borel _
local instance averagingRotationBorelSpace : BorelSpace (rotationGroup X hX) := ⟨rfl⟩

 

def rotationHaar : Measure (rotationGroup X hX) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (rotationGroup X hX))

instance rotationHaar_probability : IsProbabilityMeasure (rotationHaar X hX) :=
  ⟨by exact Measure.haarMeasure_self⟩


def rotationEvaluation (j : J) : rotationGroup X hX →* Matrix (I j) (I j) ℂ where
  toFun g := (g.val j).val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rotationEvaluation_continuous (j : J) : Continuous (rotationEvaluation X hX j) := by
  unfold rotationEvaluation
  exact continuous_subtype_val.comp ((continuous_apply j).comp continuous_subtype_val)



theorem rotationOrbit_integrable (j : J) (M : Matrix (I j) (I j) ℂ) :
    Integrable (fun g => rotationEvaluation X hX j g * M *
      (rotationEvaluation X hX j g)ᴴ) (rotationHaar X hX) := by
  have hc : Continuous (fun g => rotationEvaluation X hX j g * M *
      (rotationEvaluation X hX j g)ᴴ) :=
    ((rotationEvaluation_continuous X hX j).mul continuous_const).mul
      (rotationEvaluation_continuous X hX j).matrix_conjTranspose
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

 
def rotationAverage (j : J) (M : Matrix (I j) (I j) ℂ) : Matrix (I j) (I j) ℂ :=
  matrixConjugationAverage (rotationHaar X hX) (rotationEvaluation X hX j) M

theorem rotationAverage_add (j : J) (M N : Matrix (I j) (I j) ℂ) :
    rotationAverage X hX j (M+N) = rotationAverage X hX j M + rotationAverage X hX j N := by
  simp only [rotationAverage, matrixConjugationAverage, Matrix.mul_add, Matrix.add_mul]
  exact integral_add (rotationOrbit_integrable X hX j M) (rotationOrbit_integrable X hX j N)

theorem rotationAverage_smul (j : J) (c : ℂ) (M : Matrix (I j) (I j) ℂ) :
    rotationAverage X hX j (c • M) = c • rotationAverage X hX j M := by
  simp only [rotationAverage, matrixConjugationAverage, Matrix.mul_smul, Matrix.smul_mul,
    integral_smul]

 
def rotationAverageLinear (j : J) : Matrix (I j) (I j) ℂ →ₗ[ℂ] Matrix (I j) (I j) ℂ where
  toFun := rotationAverage X hX j
  map_add' := rotationAverage_add X hX j
  map_smul' := rotationAverage_smul X hX j

end
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SpinSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Schur. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
open NormedSpace MeasureTheory


def spinLowerMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j =>
  if i.val = j.val+1 then (spinStep n i.val : ℂ) else 0

 
def spinWeightMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  Matrix.diagonal (fun i => (n : ℂ) - 2 * (i.val : ℂ))

 
def spinGenerator (n : ℕ) (s : Fin 3) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  if s = 0 then spinLowerMatrix n - (spinLowerMatrix n)ᴴ
  else if s = 1 then Complex.I • (spinLowerMatrix n + (spinLowerMatrix n)ᴴ)
  else Complex.I • spinWeightMatrix n

theorem spinWeightMatrix_adjoint (n : ℕ) : (spinWeightMatrix n)ᴴ = spinWeightMatrix n := by
  simp [spinWeightMatrix, Matrix.diagonal_conjTranspose]

theorem spinGenerator_skew (n : ℕ) (s : Fin 3) :
    (spinGenerator n s)ᴴ = -spinGenerator n s := by
  fin_cases s <;> simp [spinGenerator, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, spinWeightMatrix_adjoint, sub_eq_add_neg, add_comm]



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FockRotations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fock Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def sectorOneBodyLinear (Q k : ℕ) :
    Matrix (Orbital Q) (Orbital Q) ℂ →ₗ[ℂ]
      Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ where
  toFun := sectorOneBody Q k
  map_add' A B := by ext S T; exact congrFun (congrFun (oneBodyLift_add Q A B) S.val) T.val
  map_smul' c A := by ext S T; exact congrFun (congrFun (oneBodyLift_smul Q c A) S.val) T.val

 

inductive FockRotationIndex
  | spin (n : ℕ)
  | sector (k : ℕ)
  | fock
  deriving DecidableEq

 

abbrev FockRotationSpace (Q : ℕ) : FockRotationIndex → Type
  | .spin n => Fin (n+1)
  | .sector k => SectorOccupation Q k
  | .fock => Occupation Q

instance instFintypeFockRotationSpace (Q : ℕ) (j : FockRotationIndex) : Fintype (FockRotationSpace Q j) := by
  cases j <;> unfold FockRotationSpace <;> infer_instance
instance instDecidableEqFockRotationSpace (Q : ℕ) (j : FockRotationIndex) : DecidableEq (FockRotationSpace Q j) := by
  cases j <;> unfold FockRotationSpace <;> infer_instance

 
def fockRotationGenerator (Q : ℕ) (s : Fin 3) :
    ∀ j, Matrix (FockRotationSpace Q j) (FockRotationSpace Q j) ℂ
  | .spin n => spinGenerator n s
  | .sector k => sectorOneBody Q k (spinGenerator Q s)
  | .fock => oneBodyLift Q (spinGenerator Q s)

theorem fockRotationGenerator_skew (Q : ℕ) (s : Fin 3) (j : FockRotationIndex) :
    (fockRotationGenerator Q s j)ᴴ = -fockRotationGenerator Q s j := by
  cases j with
  | spin n => exact spinGenerator_skew n s
  | sector k =>
    change (sectorOneBody Q k _)ᴴ = _
    rw [sectorOneBody_adjoint, spinGenerator_skew]
    exact (sectorOneBodyLinear Q k).map_neg _
  | fock =>
    change (oneBodyLift Q _)ᴴ = _
    rw [oneBodyLift_adjoint, spinGenerator_skew]
    exact (oneBodyLiftLinear Q).map_neg _

 
def fockAverage (Q : ℕ) : FockMatrix Q →ₗ[ℂ] FockMatrix Q :=
  rotationAverageLinear (fockRotationGenerator Q) (fockRotationGenerator_skew Q) .fock


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



abbrev RowEntry (t : ℕ) := { b : Fin 8 × Fin 9 // t ≤ b.1.val+b.2.val ∧ b.1.val+b.2.val ≤ t+8 }

def rowP {t : ℕ} (b : RowEntry t) : ℕ := b.val.1.val
def rowJ {t : ℕ} (b : RowEntry t) : ℕ := b.val.2.val
def rowI {t : ℕ} (b : RowEntry t) : ℕ := rowP b+rowJ b-t

theorem rowEntry_bounds {t : ℕ} (b : RowEntry t) :
    rowP b ≤ 7 ∧ rowJ b ≤ 8 ∧ rowI b ≤ 8 ∧ t+rowI b = rowP b+rowJ b := by
  have hp := b.val.1.isLt
  have hj := b.val.2.isLt
  have ht := b.property
  dsimp [rowP, rowJ, rowI]
  omega


def rowFourLevel {t : ℕ} (b c : RowEntry t) : ℕ := rowP b+rowJ b+rowI c



def rowFourTrace (Q D t : ℕ) (a : RowEntry t → ℝ) : Matrix (CopyLabel D) (CopyLabel D) ℝ :=
  fun r s => -(∑ b : RowEntry t, ∑ c : RowEntry t,
    a b*a c*sphericalCopyCoefficient Q D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      sphericalCopyCoefficient Q D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b))


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativeTransfer
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Transfer. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 

structure ComparisonRow where
  t : Fin 8
  ell : ℝ
  alpha : RowEntry t.val → ℝ

 
def fourSpinRatio (Q D : ℕ) : ℝ :=
  (4 * (Q : ℝ) - 1 - 2 * (D : ℝ)) / (2 * (Q : ℝ) - 1)


def targetCopy (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ := fun r s =>
  if r.val.val=1 ∧ s.val.val=1 then 1 else 0



def fourComparison {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (Q D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
  (fourSpinRatio Q D : ℂ) • targetCopy D -
    Matrix.of (fun r s => ((∑ i, rowFourTrace Q D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ)) +
      (ε : ℂ) • 1


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



def averagedFourComparison {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (Q : ℕ) : FockMatrix Q :=
  ((2*Q-1 : ℕ) : ℂ) • ∑ D ∈ Finset.Icc 1 23,
    fockAverage Q (∑ r, ∑ s, fourComparison rows ε Q D r s •
      ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s))



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology


abbrev ComparedThreeBlock := {z : Fin 16 // z.val=2 ∨ 4 ≤ z.val}



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Three. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def rationalAlphaWeight (t : ℕ) (b : RowEntry t) : ℚ :=
  2^(rowP b) * (t.factorial : ℚ) * (rowI b).factorial /
    (2^t * ((rowP b).factorial : ℚ) * (rowJ b).factorial)



def rationalComparisonRow (t : Fin 8) (ell : ℚ) (a : RowEntry t.val → ℚ) : ComparisonRow where
  t := t
  ell := ell
  alpha b := (a b : ℝ) * Real.sqrt (rationalAlphaWeight t.val b : ℝ)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CertificateRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate Rows. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def certificateEllData : Fin 8 → ℤ := ![711263444, 341669889, 383742518, 275246624, 176011065, 178799366, 29656603, 153354554]

def certificateAlphaData : Fin 8 → Fin 8 → Fin 9 → ℤ := ![
  ![![-1458000, -1303000, 1475944, 3608220, 43844714, -184490641, -142169573, 1489137, -100397507],
    ![781353, -3890972, -194326, -13071015, -49364910, 44700932, 51534774, -41946820, 0],
    ![2056486, -760626, 4305543, -36416268, -8021896, -2613330, -1141300, 0, 0],
    ![3923145, -4779646, 49466660, -6088990, 5250044, -9079480, 0, 0, 0],
    ![3991791, -6855540, 9257380, -9310399, 6494980, 0, 0, 0, 0],
    ![-39241199, -7152680, 9042278, -4542700, 0, 0, 0, 0, 0],
    ![5245792, -12421683, 8099967, 0, 0, 0, 0, 0, 0],
    ![21052655, -7572580, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, -2158090, 10930045, -20794124, -10149386, 597895303, 834366316, 765947384, 1283859555],
    ![-5627000, -5402022, 9973000, 24359402, 91996112, -136745470, -141127842, -50782825, -366942013],
    ![-5127489, 6909968, -9505204, 72222049, 51361561, -1267754, -15925422, -78778293, 0],
    ![-5983211, -106483, -96337602, -7668424, 10264188, -19098454, 2115155, 0, 0],
    ![10208704, 618400, -7918740, -6479832, 4936997, 14394828, 0, 0, 0],
    ![99243497, -1336744, 7033004, 2815777, 3603042, 0, 0, 0, 0],
    ![35489766, -6585714, 9964326, -9564997, 0, 0, 0, 0, 0],
    ![-977099, -25775399, 1881084, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 2286849, 19304798, 72232229, -661988975, -694800860, -7185493, -295108017],
    ![0, -8424424, 2832670, -21562963, 316632327, 538338959, 592775303, 493483565, 530121321],
    ![-677288, 5188364, -2632251, -109820524, -71765788, -51844671, -17032491, -15649485, -126493796],
    ![2276756, -7542800, 36208527, 45768030, 35084799, 20746753, -6109724, -38742315, 0],
    ![14442833, -16716287, -76293178, -1636292, -4793945, -10517615, 24708653, 0, 0],
    ![10039299, 36778073, -63545981, -887901, 3332305, 4129678, 0, 0, 0],
    ![57374228, 40592205, -31810373, 4995989, -3075894, 0, 0, 0, 0],
    ![88550482, 31531302, -4435968, -7365918, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 39091021, -4327630, 213162965, 45619843, -654459233, -49355411],
    ![0, 0, -7645272, 8738979, -367337826, -305799567, -733169191, 195732122, 71375471],
    ![0, -3949210, 762818, 68452276, 199108377, 46517664, 68403288, 47754272, 127976176],
    ![11033607, -2140475, 18301715, -133068288, -15957882, -12923425, -63267429, -35729612, -80840875],
    ![8563509, 21124181, 91082225, -17834095, 23279016, 25167823, 5867255, -14358409, 0],
    ![-78804551, -37818356, 61096591, -30356506, 14193156, 7769542, -14948988, 0, 0],
    ![-10297948, -16392402, -224637, -26277133, -1390692, 7844148, 0, 0, 0],
    ![-156393617, 5235902, 12966156, -29134694, -7754810, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 19350310, -256570426, 437882921, -166877023, 644065588],
    ![0, 0, 0, 7604311, -56036955, -106906398, 395640853, -375570014, -1474842820],
    ![0, 0, 3171752, -42320168, -196928392, 84182344, 123805380, -377993673, 446685144],
    ![0, 5083588, 54525539, 112160315, -4586199, 169842096, 129314466, 473546, -43309042],
    ![8117035, -12273926, -13371505, -33864426, -63645420, 39205032, 47849173, -57278002, 30676490],
    ![-32345547, 6924448, -21143042, -30323348, 13003067, 19986152, 9072780, -25147087, 0],
    ![-62327236, -2573763, 19203739, -59245571, -6662966, 28341971, 18781561, 0, 0],
    ![135264167, 9223722, 1641094, -16817961, 11019210, 24257380, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, 160543938, -772096646, 150680285, -122410154],
    ![0, 0, 0, 0, 57714191, -84055787, -173419469, 817621606, -1272768087],
    ![0, 0, 0, 11295230, 36541316, -181828330, -133076448, 86288265, -861124623],
    ![0, 0, -24815988, -50599547, 6698654, -132907956, 35137762, 33919179, -293036253],
    ![0, -10241680, 43618923, 71239842, 27177342, -45431218, 41533885, 63934128, -214411360],
    ![31688993, 9888664, -4845107, 34212037, -3172205, 5715090, 54142081, -48900364, -147596784],
    ![-53903546, 40649652, 19129337, 39646640, -23829198, -2574933, -7391939, -19892913, 0],
    ![-165809403, -87926915, -20371590, -16611293, -44679775, 13277906, -14870629, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, -67829135, 720057917, -875530193],
    ![0, 0, 0, 0, 0, -51790296, 175876646, -200676925, -10152433],
    ![0, 0, 0, 0, -7378820, 52323471, -211371229, 182388432, -61003176],
    ![0, 0, 0, -656201, 14264883, 26191317, -100136184, -183883082, 121658379],
    ![0, 0, 2431803, -22478098, 1654355, -93663294, 109018199, 36347410, -91971370],
    ![0, 937204, -2276330, 13793516, 47941518, 28279597, -40367840, 55740134, 13007596],
    ![-10808966, -25113301, -4615426, 31886801, -27442867, 40912313, -18147728, -21491028, 127556721],
    ![78650298, 34037298, 58687256, 49941189, 61860018, 9377295, 26910871, 48292819, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 90151251, 41493601],
    ![0, 0, 0, 0, 0, 0, 5671034, 217565363, -239274251],
    ![0, 0, 0, 0, 0, -13713832, 128996036, -145424091, -81564855],
    ![0, 0, 0, 0, 4354537, 53285313, -28885070, -101829212, -59154681],
    ![0, 0, 0, 8355807, -30008008, -6707391, -116951489, -67400418, 234283414],
    ![0, 0, -7051082, -28653824, 17782076, -19218169, 30912487, -3984978, 110000521],
    ![0, 2562590, 35701498, 4486260, 45335753, -25079048, 18952126, 51942067, 32561769],
    ![-12496841, -51081249, -10849108, -40398862, -51858623, -10716483, -28108965, -5754196, -77199525]]
  ]

def certificateEll (t : Fin 8) : ℚ := certificateEllData t / 10^9

def certificateAlpha (t : Fin 8) (b : RowEntry t.val) : ℚ :=
  certificateAlphaData t b.val.1 b.val.2 / 10^9

def certificateRows (t : Fin 8) : ComparisonRow :=
  rationalComparisonRow t (certificateEll t) (certificateAlpha t)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def occupationFactorial {Q : ℕ} (A : Occupation Q) : ℚ :=
  ∏ a ∈ A, (a.val.factorial : ℚ)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FastWedge
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Wedge. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def occupationWeight {Q : ℕ} (A : Occupation Q) : ℕ := ∑ x ∈ A, x.val


end LaughlinFock
end

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def highestFourOccupations (D : ℕ) : Finset (Occupation 24) :=
  ((Finset.univ : Finset (Orbital 24)).powersetCard 4).filter
    (fun A => occupationWeight A = D+1)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Copies. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

abbrev FourSpinIndex (Q : ℕ) := (r : CopyLabel Q) × Fin (2*Q-2*r.val.val+1)

 

abbrev ValidFourCopy (Q : ℕ) :=
  {b : (D : Fin (2*Q)) × CopyLabel D.val // b.1.val + b.2.val.val ≤ 2*Q}


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_GramCache
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram Cache. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def highestLookup (xs : List (Occupation 24 × List ℚ)) (r : ℕ) (A : Occupation 24) : ℚ :=
  (((xs.find? (fun row => row.1=A)).map Prod.snd).getD []).getD (r/2) 0

def cachedFourGram (D : ℕ) (xs : List (Occupation 24 × List ℚ)) :
    Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A ∈ highestFourOccupations D,
    2 * highestLookup xs r.val.val A * highestLookup xs s.val.val A /
      (2^(2*D) * occupationFactorial A)

def boundedMatrixEntriesDecidable {ι κ : Type*} [Fintype ι] {α : Type*} [DecidableEq α]
    (s : Finset κ) (A B : ι → κ → α) : Decidable (∀ i, ∀ a∈s, A i a = B i a) :=
  @Fintype.decidableForallFintype _ _ (fun _ => Finset.decidableDforallFinset) _

def boundedEntriesDecidable {κ : Type*} {α : Type*} [DecidableEq α]
    (s : Finset κ) (A B : κ → α) : Decidable (∀ a∈s, A a = B a) :=
  Finset.decidableDforallFinset (p := fun a _ => A a = B a)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NumericTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

structure NumericRowEntry where
  p : ℕ
  j : ℕ
  i : ℕ
  a : ℤ
  deriving DecidableEq

def numericRowData_0 : List NumericRowEntry := [
  ⟨0, 0, 0, -1458000⟩,
  ⟨0, 1, 1, -1303000⟩,
  ⟨0, 2, 2, 1475944⟩,
  ⟨0, 3, 3, 3608220⟩,
  ⟨0, 4, 4, 43844714⟩,
  ⟨0, 5, 5, -184490641⟩,
  ⟨0, 6, 6, -142169573⟩,
  ⟨0, 7, 7, 1489137⟩,
  ⟨0, 8, 8, -100397507⟩,
  ⟨1, 0, 1, 781353⟩,
  ⟨1, 1, 2, -3890972⟩,
  ⟨1, 2, 3, -194326⟩,
  ⟨1, 3, 4, -13071015⟩,
  ⟨1, 4, 5, -49364910⟩,
  ⟨1, 5, 6, 44700932⟩,
  ⟨1, 6, 7, 51534774⟩,
  ⟨1, 7, 8, -41946820⟩,
  ⟨2, 0, 2, 2056486⟩,
  ⟨2, 1, 3, -760626⟩,
  ⟨2, 2, 4, 4305543⟩,
  ⟨2, 3, 5, -36416268⟩,
  ⟨2, 4, 6, -8021896⟩,
  ⟨2, 5, 7, -2613330⟩,
  ⟨2, 6, 8, -1141300⟩,
  ⟨3, 0, 3, 3923145⟩,
  ⟨3, 1, 4, -4779646⟩,
  ⟨3, 2, 5, 49466660⟩,
  ⟨3, 3, 6, -6088990⟩,
  ⟨3, 4, 7, 5250044⟩,
  ⟨3, 5, 8, -9079480⟩,
  ⟨4, 0, 4, 3991791⟩,
  ⟨4, 1, 5, -6855540⟩,
  ⟨4, 2, 6, 9257380⟩,
  ⟨4, 3, 7, -9310399⟩,
  ⟨4, 4, 8, 6494980⟩,
  ⟨5, 0, 5, -39241199⟩,
  ⟨5, 1, 6, -7152680⟩,
  ⟨5, 2, 7, 9042278⟩,
  ⟨5, 3, 8, -4542700⟩,
  ⟨6, 0, 6, 5245792⟩,
  ⟨6, 1, 7, -12421683⟩,
  ⟨6, 2, 8, 8099967⟩,
  ⟨7, 0, 7, 21052655⟩,
  ⟨7, 1, 8, -7572580⟩
]

def numericRowData_1 : List NumericRowEntry := [
  ⟨0, 1, 0, -2158090⟩,
  ⟨0, 2, 1, 10930045⟩,
  ⟨0, 3, 2, -20794124⟩,
  ⟨0, 4, 3, -10149386⟩,
  ⟨0, 5, 4, 597895303⟩,
  ⟨0, 6, 5, 834366316⟩,
  ⟨0, 7, 6, 765947384⟩,
  ⟨0, 8, 7, 1283859555⟩,
  ⟨1, 0, 0, -5627000⟩,
  ⟨1, 1, 1, -5402022⟩,
  ⟨1, 2, 2, 9973000⟩,
  ⟨1, 3, 3, 24359402⟩,
  ⟨1, 4, 4, 91996112⟩,
  ⟨1, 5, 5, -136745470⟩,
  ⟨1, 6, 6, -141127842⟩,
  ⟨1, 7, 7, -50782825⟩,
  ⟨1, 8, 8, -366942013⟩,
  ⟨2, 0, 1, -5127489⟩,
  ⟨2, 1, 2, 6909968⟩,
  ⟨2, 2, 3, -9505204⟩,
  ⟨2, 3, 4, 72222049⟩,
  ⟨2, 4, 5, 51361561⟩,
  ⟨2, 5, 6, -1267754⟩,
  ⟨2, 6, 7, -15925422⟩,
  ⟨2, 7, 8, -78778293⟩,
  ⟨3, 0, 2, -5983211⟩,
  ⟨3, 1, 3, -106483⟩,
  ⟨3, 2, 4, -96337602⟩,
  ⟨3, 3, 5, -7668424⟩,
  ⟨3, 4, 6, 10264188⟩,
  ⟨3, 5, 7, -19098454⟩,
  ⟨3, 6, 8, 2115155⟩,
  ⟨4, 0, 3, 10208704⟩,
  ⟨4, 1, 4, 618400⟩,
  ⟨4, 2, 5, -7918740⟩,
  ⟨4, 3, 6, -6479832⟩,
  ⟨4, 4, 7, 4936997⟩,
  ⟨4, 5, 8, 14394828⟩,
  ⟨5, 0, 4, 99243497⟩,
  ⟨5, 1, 5, -1336744⟩,
  ⟨5, 2, 6, 7033004⟩,
  ⟨5, 3, 7, 2815777⟩,
  ⟨5, 4, 8, 3603042⟩,
  ⟨6, 0, 5, 35489766⟩,
  ⟨6, 1, 6, -6585714⟩,
  ⟨6, 2, 7, 9964326⟩,
  ⟨6, 3, 8, -9564997⟩,
  ⟨7, 0, 6, -977099⟩,
  ⟨7, 1, 7, -25775399⟩,
  ⟨7, 2, 8, 1881084⟩
]

def numericRowData_2 : List NumericRowEntry := [
  ⟨0, 2, 0, 2286849⟩,
  ⟨0, 3, 1, 19304798⟩,
  ⟨0, 4, 2, 72232229⟩,
  ⟨0, 5, 3, -661988975⟩,
  ⟨0, 6, 4, -694800860⟩,
  ⟨0, 7, 5, -7185493⟩,
  ⟨0, 8, 6, -295108017⟩,
  ⟨1, 1, 0, -8424424⟩,
  ⟨1, 2, 1, 2832670⟩,
  ⟨1, 3, 2, -21562963⟩,
  ⟨1, 4, 3, 316632327⟩,
  ⟨1, 5, 4, 538338959⟩,
  ⟨1, 6, 5, 592775303⟩,
  ⟨1, 7, 6, 493483565⟩,
  ⟨1, 8, 7, 530121321⟩,
  ⟨2, 0, 0, -677288⟩,
  ⟨2, 1, 1, 5188364⟩,
  ⟨2, 2, 2, -2632251⟩,
  ⟨2, 3, 3, -109820524⟩,
  ⟨2, 4, 4, -71765788⟩,
  ⟨2, 5, 5, -51844671⟩,
  ⟨2, 6, 6, -17032491⟩,
  ⟨2, 7, 7, -15649485⟩,
  ⟨2, 8, 8, -126493796⟩,
  ⟨3, 0, 1, 2276756⟩,
  ⟨3, 1, 2, -7542800⟩,
  ⟨3, 2, 3, 36208527⟩,
  ⟨3, 3, 4, 45768030⟩,
  ⟨3, 4, 5, 35084799⟩,
  ⟨3, 5, 6, 20746753⟩,
  ⟨3, 6, 7, -6109724⟩,
  ⟨3, 7, 8, -38742315⟩,
  ⟨4, 0, 2, 14442833⟩,
  ⟨4, 1, 3, -16716287⟩,
  ⟨4, 2, 4, -76293178⟩,
  ⟨4, 3, 5, -1636292⟩,
  ⟨4, 4, 6, -4793945⟩,
  ⟨4, 5, 7, -10517615⟩,
  ⟨4, 6, 8, 24708653⟩,
  ⟨5, 0, 3, 10039299⟩,
  ⟨5, 1, 4, 36778073⟩,
  ⟨5, 2, 5, -63545981⟩,
  ⟨5, 3, 6, -887901⟩,
  ⟨5, 4, 7, 3332305⟩,
  ⟨5, 5, 8, 4129678⟩,
  ⟨6, 0, 4, 57374228⟩,
  ⟨6, 1, 5, 40592205⟩,
  ⟨6, 2, 6, -31810373⟩,
  ⟨6, 3, 7, 4995989⟩,
  ⟨6, 4, 8, -3075894⟩,
  ⟨7, 0, 5, 88550482⟩,
  ⟨7, 1, 6, 31531302⟩,
  ⟨7, 2, 7, -4435968⟩,
  ⟨7, 3, 8, -7365918⟩
]

def numericRowData_3 : List NumericRowEntry := [
  ⟨0, 3, 0, 39091021⟩,
  ⟨0, 4, 1, -4327630⟩,
  ⟨0, 5, 2, 213162965⟩,
  ⟨0, 6, 3, 45619843⟩,
  ⟨0, 7, 4, -654459233⟩,
  ⟨0, 8, 5, -49355411⟩,
  ⟨1, 2, 0, -7645272⟩,
  ⟨1, 3, 1, 8738979⟩,
  ⟨1, 4, 2, -367337826⟩,
  ⟨1, 5, 3, -305799567⟩,
  ⟨1, 6, 4, -733169191⟩,
  ⟨1, 7, 5, 195732122⟩,
  ⟨1, 8, 6, 71375471⟩,
  ⟨2, 1, 0, -3949210⟩,
  ⟨2, 2, 1, 762818⟩,
  ⟨2, 3, 2, 68452276⟩,
  ⟨2, 4, 3, 199108377⟩,
  ⟨2, 5, 4, 46517664⟩,
  ⟨2, 6, 5, 68403288⟩,
  ⟨2, 7, 6, 47754272⟩,
  ⟨2, 8, 7, 127976176⟩,
  ⟨3, 0, 0, 11033607⟩,
  ⟨3, 1, 1, -2140475⟩,
  ⟨3, 2, 2, 18301715⟩,
  ⟨3, 3, 3, -133068288⟩,
  ⟨3, 4, 4, -15957882⟩,
  ⟨3, 5, 5, -12923425⟩,
  ⟨3, 6, 6, -63267429⟩,
  ⟨3, 7, 7, -35729612⟩,
  ⟨3, 8, 8, -80840875⟩,
  ⟨4, 0, 1, 8563509⟩,
  ⟨4, 1, 2, 21124181⟩,
  ⟨4, 2, 3, 91082225⟩,
  ⟨4, 3, 4, -17834095⟩,
  ⟨4, 4, 5, 23279016⟩,
  ⟨4, 5, 6, 25167823⟩,
  ⟨4, 6, 7, 5867255⟩,
  ⟨4, 7, 8, -14358409⟩,
  ⟨5, 0, 2, -78804551⟩,
  ⟨5, 1, 3, -37818356⟩,
  ⟨5, 2, 4, 61096591⟩,
  ⟨5, 3, 5, -30356506⟩,
  ⟨5, 4, 6, 14193156⟩,
  ⟨5, 5, 7, 7769542⟩,
  ⟨5, 6, 8, -14948988⟩,
  ⟨6, 0, 3, -10297948⟩,
  ⟨6, 1, 4, -16392402⟩,
  ⟨6, 2, 5, -224637⟩,
  ⟨6, 3, 6, -26277133⟩,
  ⟨6, 4, 7, -1390692⟩,
  ⟨6, 5, 8, 7844148⟩,
  ⟨7, 0, 4, -156393617⟩,
  ⟨7, 1, 5, 5235902⟩,
  ⟨7, 2, 6, 12966156⟩,
  ⟨7, 3, 7, -29134694⟩,
  ⟨7, 4, 8, -7754810⟩
]

def numericRowData_4 : List NumericRowEntry := [
  ⟨0, 4, 0, 19350310⟩,
  ⟨0, 5, 1, -256570426⟩,
  ⟨0, 6, 2, 437882921⟩,
  ⟨0, 7, 3, -166877023⟩,
  ⟨0, 8, 4, 644065588⟩,
  ⟨1, 3, 0, 7604311⟩,
  ⟨1, 4, 1, -56036955⟩,
  ⟨1, 5, 2, -106906398⟩,
  ⟨1, 6, 3, 395640853⟩,
  ⟨1, 7, 4, -375570014⟩,
  ⟨1, 8, 5, -1474842820⟩,
  ⟨2, 2, 0, 3171752⟩,
  ⟨2, 3, 1, -42320168⟩,
  ⟨2, 4, 2, -196928392⟩,
  ⟨2, 5, 3, 84182344⟩,
  ⟨2, 6, 4, 123805380⟩,
  ⟨2, 7, 5, -377993673⟩,
  ⟨2, 8, 6, 446685144⟩,
  ⟨3, 1, 0, 5083588⟩,
  ⟨3, 2, 1, 54525539⟩,
  ⟨3, 3, 2, 112160315⟩,
  ⟨3, 4, 3, -4586199⟩,
  ⟨3, 5, 4, 169842096⟩,
  ⟨3, 6, 5, 129314466⟩,
  ⟨3, 7, 6, 473546⟩,
  ⟨3, 8, 7, -43309042⟩,
  ⟨4, 0, 0, 8117035⟩,
  ⟨4, 1, 1, -12273926⟩,
  ⟨4, 2, 2, -13371505⟩,
  ⟨4, 3, 3, -33864426⟩,
  ⟨4, 4, 4, -63645420⟩,
  ⟨4, 5, 5, 39205032⟩,
  ⟨4, 6, 6, 47849173⟩,
  ⟨4, 7, 7, -57278002⟩,
  ⟨4, 8, 8, 30676490⟩,
  ⟨5, 0, 1, -32345547⟩,
  ⟨5, 1, 2, 6924448⟩,
  ⟨5, 2, 3, -21143042⟩,
  ⟨5, 3, 4, -30323348⟩,
  ⟨5, 4, 5, 13003067⟩,
  ⟨5, 5, 6, 19986152⟩,
  ⟨5, 6, 7, 9072780⟩,
  ⟨5, 7, 8, -25147087⟩,
  ⟨6, 0, 2, -62327236⟩,
  ⟨6, 1, 3, -2573763⟩,
  ⟨6, 2, 4, 19203739⟩,
  ⟨6, 3, 5, -59245571⟩,
  ⟨6, 4, 6, -6662966⟩,
  ⟨6, 5, 7, 28341971⟩,
  ⟨6, 6, 8, 18781561⟩,
  ⟨7, 0, 3, 135264167⟩,
  ⟨7, 1, 4, 9223722⟩,
  ⟨7, 2, 5, 1641094⟩,
  ⟨7, 3, 6, -16817961⟩,
  ⟨7, 4, 7, 11019210⟩,
  ⟨7, 5, 8, 24257380⟩
]

def numericRowData_5 : List NumericRowEntry := [
  ⟨0, 5, 0, 160543938⟩,
  ⟨0, 6, 1, -772096646⟩,
  ⟨0, 7, 2, 150680285⟩,
  ⟨0, 8, 3, -122410154⟩,
  ⟨1, 4, 0, 57714191⟩,
  ⟨1, 5, 1, -84055787⟩,
  ⟨1, 6, 2, -173419469⟩,
  ⟨1, 7, 3, 817621606⟩,
  ⟨1, 8, 4, -1272768087⟩,
  ⟨2, 3, 0, 11295230⟩,
  ⟨2, 4, 1, 36541316⟩,
  ⟨2, 5, 2, -181828330⟩,
  ⟨2, 6, 3, -133076448⟩,
  ⟨2, 7, 4, 86288265⟩,
  ⟨2, 8, 5, -861124623⟩,
  ⟨3, 2, 0, -24815988⟩,
  ⟨3, 3, 1, -50599547⟩,
  ⟨3, 4, 2, 6698654⟩,
  ⟨3, 5, 3, -132907956⟩,
  ⟨3, 6, 4, 35137762⟩,
  ⟨3, 7, 5, 33919179⟩,
  ⟨3, 8, 6, -293036253⟩,
  ⟨4, 1, 0, -10241680⟩,
  ⟨4, 2, 1, 43618923⟩,
  ⟨4, 3, 2, 71239842⟩,
  ⟨4, 4, 3, 27177342⟩,
  ⟨4, 5, 4, -45431218⟩,
  ⟨4, 6, 5, 41533885⟩,
  ⟨4, 7, 6, 63934128⟩,
  ⟨4, 8, 7, -214411360⟩,
  ⟨5, 0, 0, 31688993⟩,
  ⟨5, 1, 1, 9888664⟩,
  ⟨5, 2, 2, -4845107⟩,
  ⟨5, 3, 3, 34212037⟩,
  ⟨5, 4, 4, -3172205⟩,
  ⟨5, 5, 5, 5715090⟩,
  ⟨5, 6, 6, 54142081⟩,
  ⟨5, 7, 7, -48900364⟩,
  ⟨5, 8, 8, -147596784⟩,
  ⟨6, 0, 1, -53903546⟩,
  ⟨6, 1, 2, 40649652⟩,
  ⟨6, 2, 3, 19129337⟩,
  ⟨6, 3, 4, 39646640⟩,
  ⟨6, 4, 5, -23829198⟩,
  ⟨6, 5, 6, -2574933⟩,
  ⟨6, 6, 7, -7391939⟩,
  ⟨6, 7, 8, -19892913⟩,
  ⟨7, 0, 2, -165809403⟩,
  ⟨7, 1, 3, -87926915⟩,
  ⟨7, 2, 4, -20371590⟩,
  ⟨7, 3, 5, -16611293⟩,
  ⟨7, 4, 6, -44679775⟩,
  ⟨7, 5, 7, 13277906⟩,
  ⟨7, 6, 8, -14870629⟩
]

def numericRowData_6 : List NumericRowEntry := [
  ⟨0, 6, 0, -67829135⟩,
  ⟨0, 7, 1, 720057917⟩,
  ⟨0, 8, 2, -875530193⟩,
  ⟨1, 5, 0, -51790296⟩,
  ⟨1, 6, 1, 175876646⟩,
  ⟨1, 7, 2, -200676925⟩,
  ⟨1, 8, 3, -10152433⟩,
  ⟨2, 4, 0, -7378820⟩,
  ⟨2, 5, 1, 52323471⟩,
  ⟨2, 6, 2, -211371229⟩,
  ⟨2, 7, 3, 182388432⟩,
  ⟨2, 8, 4, -61003176⟩,
  ⟨3, 3, 0, -656201⟩,
  ⟨3, 4, 1, 14264883⟩,
  ⟨3, 5, 2, 26191317⟩,
  ⟨3, 6, 3, -100136184⟩,
  ⟨3, 7, 4, -183883082⟩,
  ⟨3, 8, 5, 121658379⟩,
  ⟨4, 2, 0, 2431803⟩,
  ⟨4, 3, 1, -22478098⟩,
  ⟨4, 4, 2, 1654355⟩,
  ⟨4, 5, 3, -93663294⟩,
  ⟨4, 6, 4, 109018199⟩,
  ⟨4, 7, 5, 36347410⟩,
  ⟨4, 8, 6, -91971370⟩,
  ⟨5, 1, 0, 937204⟩,
  ⟨5, 2, 1, -2276330⟩,
  ⟨5, 3, 2, 13793516⟩,
  ⟨5, 4, 3, 47941518⟩,
  ⟨5, 5, 4, 28279597⟩,
  ⟨5, 6, 5, -40367840⟩,
  ⟨5, 7, 6, 55740134⟩,
  ⟨5, 8, 7, 13007596⟩,
  ⟨6, 0, 0, -10808966⟩,
  ⟨6, 1, 1, -25113301⟩,
  ⟨6, 2, 2, -4615426⟩,
  ⟨6, 3, 3, 31886801⟩,
  ⟨6, 4, 4, -27442867⟩,
  ⟨6, 5, 5, 40912313⟩,
  ⟨6, 6, 6, -18147728⟩,
  ⟨6, 7, 7, -21491028⟩,
  ⟨6, 8, 8, 127556721⟩,
  ⟨7, 0, 1, 78650298⟩,
  ⟨7, 1, 2, 34037298⟩,
  ⟨7, 2, 3, 58687256⟩,
  ⟨7, 3, 4, 49941189⟩,
  ⟨7, 4, 5, 61860018⟩,
  ⟨7, 5, 6, 9377295⟩,
  ⟨7, 6, 7, 26910871⟩,
  ⟨7, 7, 8, 48292819⟩
]

def numericRowData_7 : List NumericRowEntry := [
  ⟨0, 7, 0, 90151251⟩,
  ⟨0, 8, 1, 41493601⟩,
  ⟨1, 6, 0, 5671034⟩,
  ⟨1, 7, 1, 217565363⟩,
  ⟨1, 8, 2, -239274251⟩,
  ⟨2, 5, 0, -13713832⟩,
  ⟨2, 6, 1, 128996036⟩,
  ⟨2, 7, 2, -145424091⟩,
  ⟨2, 8, 3, -81564855⟩,
  ⟨3, 4, 0, 4354537⟩,
  ⟨3, 5, 1, 53285313⟩,
  ⟨3, 6, 2, -28885070⟩,
  ⟨3, 7, 3, -101829212⟩,
  ⟨3, 8, 4, -59154681⟩,
  ⟨4, 3, 0, 8355807⟩,
  ⟨4, 4, 1, -30008008⟩,
  ⟨4, 5, 2, -6707391⟩,
  ⟨4, 6, 3, -116951489⟩,
  ⟨4, 7, 4, -67400418⟩,
  ⟨4, 8, 5, 234283414⟩,
  ⟨5, 2, 0, -7051082⟩,
  ⟨5, 3, 1, -28653824⟩,
  ⟨5, 4, 2, 17782076⟩,
  ⟨5, 5, 3, -19218169⟩,
  ⟨5, 6, 4, 30912487⟩,
  ⟨5, 7, 5, -3984978⟩,
  ⟨5, 8, 6, 110000521⟩,
  ⟨6, 1, 0, 2562590⟩,
  ⟨6, 2, 1, 35701498⟩,
  ⟨6, 3, 2, 4486260⟩,
  ⟨6, 4, 3, 45335753⟩,
  ⟨6, 5, 4, -25079048⟩,
  ⟨6, 6, 5, 18952126⟩,
  ⟨6, 7, 6, 51942067⟩,
  ⟨6, 8, 7, 32561769⟩,
  ⟨7, 0, 0, -12496841⟩,
  ⟨7, 1, 1, -51081249⟩,
  ⟨7, 2, 2, -10849108⟩,
  ⟨7, 3, 3, -40398862⟩,
  ⟨7, 4, 4, -51858623⟩,
  ⟨7, 5, 5, -10716483⟩,
  ⟨7, 6, 6, -28108965⟩,
  ⟨7, 7, 7, -5754196⟩,
  ⟨7, 8, 8, -77199525⟩
]

def numericRowData (t : Fin 8) : List NumericRowEntry :=
 ![numericRowData_0, numericRowData_1, numericRowData_2, numericRowData_3, numericRowData_4, numericRowData_5, numericRowData_6, numericRowData_7] t

def numericRowFactor (D t : ℕ) (b c : NumericRowEntry) : ℕ :=
  2 * 2^(53+b.p+c.p-(t+2*(b.p+b.j+c.i))) *
    t.factorial * b.i.factorial * c.i.factorial *
      ((23).factorial / ((b.p+b.j+c.i)-D).factorial)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SparseTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
structure CollectedFourTerm where
  p : ℕ
  j : ℕ
  k : ℕ
  q : ℕ
  l : ℕ
  i : ℕ
  a : ℤ
  deriving DecidableEq

def collectFourTerm (D t : ℕ) (b c : NumericRowEntry) : CollectedFourTerm :=
  ⟨b.p,b.j,c.i,c.p,c.j,b.i,b.a*c.a*(numericRowFactor D t b c : ℤ)⟩

def collectNumericRow (D : ℕ) (t : Fin 8) : List CollectedFourTerm :=
  (numericRowData t).flatMap fun b => (numericRowData t).flatMap fun c =>
    if D ≤ b.p+b.j+c.i then [collectFourTerm D t.val b c] else []

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PartsTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parts Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def collectNumericRowParts (D : ℕ) (t : Fin 8) : List (List CollectedFourTerm) :=
  (numericRowData t).map fun b => (numericRowData t).flatMap fun c =>
    if D ≤ b.p+b.j+c.i then [collectFourTerm D t.val b c] else []

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1001. -/
namespace LaughlinFock

def collectedFourData_10_0_0 : List CollectedFourTerm := [

]

def collectedFourData_10_0_1 : List CollectedFourTerm := [

]

def collectedFourData_10_0_2 : List CollectedFourTerm := [
  ⟨0, 2, 8, 0, 8, 2, -5307104128847786389487343432349438002920108851200000⟩,
  ⟨0, 2, 8, 1, 7, 2, -4434694610774247672868520275806132377562906624000000⟩,
  ⟨0, 2, 8, 2, 6, 2, -241320651209157159901267471087321464774328320000000⟩,
  ⟨0, 2, 8, 3, 5, 2, -3839596996829086568264890875997395063505158144000000⟩,
  ⟨0, 2, 8, 4, 4, 2, 5493289417998603593850991673925282282589913088000000⟩,
  ⟨0, 2, 8, 5, 3, 2, -7684200979569531098105583043255061547570954240000000⟩,
  ⟨0, 2, 8, 6, 2, 2, 27402986926665144561661120111883052421816831180800000⟩,
  ⟨0, 2, 8, 7, 1, 2, -51237569422474422526596408340143451228480733184000000⟩
]

def collectedFourData_10_0_3 : List CollectedFourTerm := [
  ⟨0, 3, 7, 0, 7, 3, 72164520751697383330746241114596830437441536000000⟩,
  ⟨0, 3, 8, 0, 8, 3, -9730653361403528761732841313494222608156065792000000⟩,
  ⟨0, 3, 7, 1, 6, 3, 4994815477363109997725360107485417067348230144000000⟩,
  ⟨0, 3, 8, 1, 7, 3, -8131077697640216670583869829869495201394851840000000⟩,
  ⟨0, 3, 7, 2, 5, 3, -506574497889806841894974268430666446101544960000000⟩,
  ⟨0, 3, 8, 2, 6, 3, -442464958073903065173349047047192367543091200000000⟩,
  ⟨0, 3, 7, 3, 4, 3, 2035363618983743401292342175024822576067117056000000⟩,
  ⟨0, 3, 8, 3, 5, 3, -7039957482752723038955785868192486037431255040000000⟩,
  ⟨0, 3, 7, 4, 3, 3, -7219005175127151536120010153823066278070321152000000⟩,
  ⟨0, 3, 8, 4, 4, 3, 10072026823414838973940589130256982330132398080000000⟩,
  ⟨0, 3, 7, 5, 2, 3, 14022224327214846439497205903568886381504626688000000⟩,
  ⟨0, 3, 8, 5, 3, 3, -14089095347707487631038098421247915661354598400000000⟩,
  ⟨0, 3, 7, 6, 1, 3, -38525607274527745191004517029859350772906459136000000⟩,
  ⟨0, 3, 8, 6, 2, 3, 50243778975624265509197954060299036113216995328000000⟩,
  ⟨0, 3, 7, 7, 0, 3, 130588796802514265970903813995455142486888939520000000⟩,
  ⟨0, 3, 8, 7, 1, 3, -93944836020994357263342490891120735403051581440000000⟩
]

def collectedFourData_10_0_4 : List CollectedFourTerm := [
  ⟨0, 4, 6, 0, 6, 4, -47838980931703452830730512304231251696252721561600000⟩,
  ⟨0, 4, 7, 0, 7, 4, 876895747295130781018046667953877328942281523200000⟩,
  ⟨0, 4, 8, 0, 8, 4, -59120246778726956386937405673370599756519387955200000⟩,
  ⟨0, 4, 6, 1, 5, 4, 30083047848464350232685753945910838380995595468800000⟩,
  ⟨0, 4, 7, 1, 6, 4, 60693709387941708654352856660543805668335602892800000⟩,
  ⟨0, 4, 8, 1, 7, 4, -49401751579007623540108694273610904328107720704000000⟩,
  ⟨0, 4, 6, 2, 4, 4, -10797228174276311611318570218432419743067327692800000⟩,
  ⟨0, 4, 7, 2, 5, 4, -6155559799477910021597453823963560747049418752000000⟩,
  ⟨0, 4, 8, 2, 6, 4, -2688271438794235212410669165122511079965982720000000⟩,
  ⟨0, 4, 6, 3, 3, 4, -16391190905712743879552330490031987323530379264000000⟩,
  ⟨0, 4, 7, 3, 4, 4, 24732398734098031738377918490031452835028349747200000⟩,
  ⟨0, 4, 8, 3, 5, 4, -42772464318064457594634929416185992991026970624000000⟩,
  ⟨0, 4, 6, 4, 2, 4, 49840608332983644557041530116427295432938356736000000⟩,
  ⟨0, 4, 7, 4, 3, 4, -87720598319384592052547382053053402388168599142400000⟩,
  ⟨0, 4, 8, 4, 4, 4, 61194319563794906930353274385656381369166594048000000⟩,
  ⟨0, 4, 6, 5, 1, 4, -77018318878811381784103020861878239306859937792000000⟩,
  ⟨0, 4, 7, 5, 2, 4, 170388838615876348641067700040765087133147437465600000⟩,
  ⟨0, 4, 8, 5, 3, 4, -85600705616476455266225860449676902360196055040000000⟩,
  ⟨0, 4, 6, 6, 0, 4, 112970825208989558059914145191193782674469263769600000⟩,
  ⟨0, 4, 7, 6, 1, 4, -468137816604305855231795295708774047830720590643200000⟩,
  ⟨0, 4, 8, 6, 2, 4, 305264662280218347649374021700305135615299341516800000⟩,
  ⟨0, 4, 7, 7, 0, 4, 1586829086754785593011016525084370693074949505024000000⟩,
  ⟨0, 4, 8, 7, 1, 4, -570777899784020318858755036717383333501902782464000000⟩
]

def collectedFourData_10_0_5 : List CollectedFourTerm := [
  ⟨0, 5, 5, 0, 5, 5, 217683470486240658578067546849306730344757592064000000⟩,
  ⟨0, 5, 6, 0, 6, 5, 251622243928787722125828461136330215247669362688000000⟩,
  ⟨0, 5, 7, 0, 7, 5, -2306136871320632487887394794312106056444018688000000⟩,
  ⟨0, 5, 8, 0, 8, 5, 103653052150953337155279482489394070967090675712000000⟩,
  ⟨0, 5, 5, 1, 4, 5, 116492900353042042377065971862895856119479009280000000⟩,
  ⟨0, 5, 6, 1, 5, 5, -158230042873493793347491498548986141800277213184000000⟩,
  ⟨0, 5, 7, 1, 6, 5, -159617607347847614827023474903451960542077386752000000⟩,
  ⟨0, 5, 8, 1, 7, 5, 86614021621605653256944328342251864957638410240000000⟩,
  ⟨0, 5, 5, 2, 3, 5, 171872558031754686900901530461199048171520524288000000⟩,
  ⟨0, 5, 6, 2, 4, 5, 56790983597689120525678017731000227689350037504000000⟩,
  ⟨0, 5, 7, 2, 5, 5, 16188427713308711017376548800599692628648263680000000⟩,
  ⟨0, 5, 8, 2, 6, 5, 4713233702899935301991929873921887450641203200000000⟩,
  ⟨0, 5, 5, 3, 2, 5, -466932053086114057614764352063960892874812293120000000⟩,
  ⟨0, 5, 6, 3, 3, 5, 86213965181421718254549346733959920796324331520000000⟩,
  ⟨0, 5, 7, 3, 4, 5, -65043418003612340136539698982750446891038670848000000⟩,
  ⟨0, 5, 8, 3, 5, 5, 74991169965488310831034237188602994252778045440000000⟩,
  ⟨0, 5, 5, 4, 1, 5, 129423388084579729722618086854805497664042434560000000⟩,
  ⟨0, 5, 6, 4, 2, 5, -262150352354393679784430597346366438959984148480000000⟩,
  ⟨0, 5, 7, 4, 3, 5, 230695275672895056877580102897918866197646934016000000⟩,
  ⟨0, 5, 8, 4, 4, 5, -107289437082838944318694627854289601521652858880000000⟩,
  ⟨0, 5, 5, 5, 0, 5, 1481642270946190090178591663754775448798701289472000000⟩,
  ⟨0, 5, 6, 5, 1, 5, 405098976660399505155994686407473453746156994560000000⟩,
  ⟨0, 5, 7, 5, 2, 5, -448103419825714057821343909680259247665739464704000000⟩,
  ⟨0, 5, 8, 5, 3, 5, 150080131374142021178366703501375330742330982400000000⟩,
  ⟨0, 5, 6, 6, 0, 5, -594201046593251883476200718611438784867758768128000000⟩,
  ⟨0, 5, 7, 6, 1, 5, 1231149635587610837645205042364061740265518399488000000⟩,
  ⟨0, 5, 8, 6, 2, 5, -535207744947372718805147340682820628096491716608000000⟩,
  ⟨0, 5, 7, 7, 0, 5, -4173181449148508014446273369099980448142102364160000000⟩,
  ⟨0, 5, 8, 7, 1, 5, 1000720982007352796121140406894969777509200035840000000⟩
]

def collectedFourData_10_0_6 : List CollectedFourTerm := [
  ⟨0, 6, 4, 0, 4, 6, -47838980931703452830730512304231251696252721561600000⟩,
  ⟨0, 6, 5, 0, 5, 6, 251622243928787722125828461136330215247669362688000000⟩,
  ⟨0, 6, 6, 0, 6, 6, 145426185778676950050294223018333873730589032448000000⟩,
  ⟨0, 6, 7, 0, 7, 6, -888561318064937144678462551359922227099205632000000⟩,
  ⟨0, 6, 8, 0, 8, 6, 29953369350957552407003504966096353564060286976000000⟩,
  ⟨0, 6, 4, 1, 3, 6, 28523576974091326379835479701671278065150328832000000⟩,
  ⟨0, 6, 5, 1, 4, 6, 134655171213185305284364323493606798254680309760000000⟩,
  ⟨0, 6, 6, 1, 5, 6, -91449751227880601345909629244442863212758564864000000⟩,
  ⟨0, 6, 7, 1, 6, 6, -61501133490899296807761636775927244613671190528000000⟩,
  ⟨0, 6, 8, 1, 7, 6, 25029477924349919932915122328325340700103147520000000⟩,
  ⟨0, 6, 4, 2, 2, 6, -18791117166610258140690067417285170214319475916800000⟩,
  ⟨0, 6, 5, 2, 3, 6, 198669006080847355374383440139235803402229252096000000⟩,
  ⟨0, 6, 6, 2, 4, 6, 32822599474030227576210136790771128737762115584000000⟩,
  ⟨0, 6, 7, 2, 5, 6, 6237448802463822168954411956308722578903531520000000⟩,
  ⟨0, 6, 8, 2, 6, 6, 1362017104279207034976001952630388255463833600000000⟩,
  ⟨0, 6, 4, 3, 1, 6, 41720585766264582135687284029334926941475779379200000⟩,
  ⟨0, 6, 5, 3, 2, 6, -539730879415716549548888334356388751682347991040000000⟩,
  ⟨0, 6, 6, 3, 3, 6, 49827741464455613837244402275381654205675601920000000⟩,
  ⟨0, 6, 7, 3, 4, 6, -25061420226823535332457896067275752486702415872000000⟩,
  ⟨0, 6, 8, 3, 5, 6, 21670738732955357381799544745235358902512517120000000⟩,
  ⟨0, 6, 4, 4, 0, 6, -69687110207117038620850698651215130723338315366400000⟩,
  ⟨0, 6, 5, 4, 1, 6, 149601636054248313271782891010373344095130091520000000⟩,
  ⟨0, 6, 6, 4, 2, 6, -151510952482504359647373237511006790292162478080000000⟩,
  ⟨0, 6, 7, 4, 3, 6, 88887568111199683863899298019928251525679284224000000⟩,
  ⟨0, 6, 8, 4, 4, 6, -31004201706655091940868950012425546697529098240000000⟩,
  ⟨0, 6, 5, 5, 0, 6, 1712643371967877907943757460661996417476223565824000000⟩,
  ⟨0, 6, 6, 5, 1, 6, 234128740443313180006129943565075226205890805760000000⟩,
  ⟨0, 6, 7, 5, 2, 6, -172655565374889401627039102556408332306513657856000000⟩,
  ⟨0, 6, 8, 5, 3, 6, 43369736963877359486799152336557012025553715200000000⟩,
  ⟨0, 6, 6, 6, 0, 6, -343421115885964067502171608100494668020672626688000000⟩,
  ⟨0, 6, 7, 6, 1, 6, 474365574974061250289089532650996556945090936832000000⟩,
  ⟨0, 6, 8, 6, 2, 6, -154662838490803620705840169746663742279079952384000000⟩,
  ⟨0, 6, 7, 7, 0, 6, -1607939084229656392165997505332033657524967178240000000⟩,
  ⟨0, 6, 8, 7, 1, 6, 289185552854397970284232306778580930393349816320000000⟩
]

def collectedFourData_10_0_7 : List CollectedFourTerm := [
  ⟨0, 7, 3, 0, 3, 7, 72164520751697383330746241114596830437441536000000⟩,
  ⟨0, 7, 4, 0, 4, 7, 876895747295130781018046667953877328942281523200000⟩,
  ⟨0, 7, 5, 0, 5, 7, -2306136871320632487887394794312106056444018688000000⟩,
  ⟨0, 7, 6, 0, 6, 7, -888561318064937144678462551359922227099205632000000⟩,
  ⟨0, 7, 7, 0, 7, 7, 4071865797760601056012070273649210940194816000000⟩,
  ⟨0, 7, 8, 0, 8, 7, -109809957024432413900179558330278160011519590400000⟩,
  ⟨0, 7, 3, 1, 2, 7, -7773053006520858325229943878607814197352857600000⟩,
  ⟨0, 7, 4, 1, 3, 7, -522841474861980573788147107882840785539825664000000⟩,
  ⟨0, 7, 5, 1, 4, 7, -1234124815040613403339384941002894855645429760000000⟩,
  ⟨0, 7, 6, 1, 5, 7, 558762584968179188222589883883049870296088576000000⟩,
  ⟨0, 7, 7, 1, 6, 7, 281831266896091201179936275607456185805963264000000⟩,
  ⟨0, 7, 8, 1, 7, 7, -91758822288517623610640648695782426707755008000000⟩,
  ⟨0, 7, 3, 2, 1, 7, -60850181819601436601240711923365347731911475200000⟩,
  ⟨0, 7, 4, 2, 2, 7, 344444016352467872710656404772729579806235033600000⟩,
  ⟨0, 7, 5, 2, 3, 7, -1820816446742003928717752629012211623155204096000000⟩,
  ⟨0, 7, 6, 2, 4, 7, -200547735573204458344897189130727843541549056000000⟩,
  ⟨0, 7, 7, 2, 5, 7, -28583344703037293567235314435772376688885760000000⟩,
  ⟨0, 7, 8, 2, 6, 7, -4993195855031926798113619690670066698813440000000⟩,
  ⟨0, 7, 3, 3, 0, 7, 627704250327126019870408039637328061695787008000000⟩,
  ⟨0, 7, 4, 3, 1, 7, -764744639634539781825427381608479044432979558400000⟩,
  ⟨0, 7, 5, 3, 2, 7, 4946674277188141083569865273588892096832471040000000⟩,
  ⟨0, 7, 6, 3, 3, 7, -304450009431158472963871766885312532609761280000000⟩,
  ⟨0, 7, 7, 3, 4, 7, 114844904668076917089615440179112589379239936000000⟩,
  ⟨0, 7, 8, 3, 5, 7, -79445582934978145491871808830360215877582848000000⟩,
  ⟨0, 7, 4, 4, 0, 7, 1277375257410862306636392985195260139874864332800000⟩,
  ⟨0, 7, 5, 4, 1, 7, -1371110294256147017973582779904670876324331520000000⟩,
  ⟨0, 7, 6, 4, 2, 7, 925739549024655262842043497305383826588958720000000⟩,
  ⟨0, 7, 7, 4, 3, 7, -407330637829610060713486783969113277162586112000000⟩,
  ⟨0, 7, 8, 4, 4, 7, 113662340189311360431830360531002435143991296000000⟩,
  ⟨0, 7, 5, 5, 0, 7, -15696505864703297509914007827016512451928653824000000⟩,
  ⟨0, 7, 6, 5, 1, 7, -1430538393696201561440715987094895702405283840000000⟩,
  ⟨0, 7, 7, 5, 2, 7, 791200648902941925597007357036935939178364928000000⟩,
  ⟨0, 7, 8, 5, 3, 7, -158994766043308745225905477394598524438446080000000⟩,
  ⟨0, 7, 6, 6, 0, 7, 2098320311084624107717167942470376730543521792000000⟩,
  ⟨0, 7, 7, 6, 1, 7, -2173798162380462615101108622800722899203260416000000⟩,
  ⟨0, 7, 8, 6, 2, 7, 566998638749431574676400339892792403724704153600000⟩,
  ⟨0, 7, 7, 7, 0, 7, 7368441579491258660540834917997626078129029120000000⟩,
  ⟨0, 7, 8, 7, 1, 7, -1060162973953145871770345653473739312912662528000000⟩
]

def collectedFourData_10_0_8 : List CollectedFourTerm := [
  ⟨0, 8, 2, 0, 2, 8, -5307104128847786389487343432349438002920108851200000⟩,
  ⟨0, 8, 3, 0, 3, 8, -9730653361403528761732841313494222608156065792000000⟩,
  ⟨0, 8, 4, 0, 4, 8, -59120246778726956386937405673370599756519387955200000⟩,
  ⟨0, 8, 5, 0, 5, 8, 103653052150953337155279482489394070967090675712000000⟩,
  ⟨0, 8, 6, 0, 6, 8, 29953369350957552407003504966096353564060286976000000⟩,
  ⟨0, 8, 7, 0, 7, 8, -109809957024432413900179558330278160011519590400000⟩,
  ⟨0, 8, 8, 0, 8, 8, 2467793075011489304559212149659167218262133964800000⟩,
  ⟨0, 8, 2, 1, 1, 8, 27981811730568543391180624264410516232456057651200000⟩,
  ⟨0, 8, 3, 1, 2, 8, 1048117323837294915583027709555447451958326067200000⟩,
  ⟨0, 8, 4, 1, 3, 8, 35249933775298054303102747282954666324267106304000000⟩,
  ⟨0, 8, 5, 1, 4, 8, 55469736165718215515008457019080054774421258240000000⟩,
  ⟨0, 8, 6, 1, 5, 8, -18835866188161621404488568018012340884149895168000000⟩,
  ⟨0, 8, 7, 1, 6, 8, -7600417313120064747058480311711685806382487961600000⟩,
  ⟨0, 8, 8, 1, 7, 8, 2062124349656479812596750064392856859570077696000000⟩,
  ⟨0, 8, 2, 2, 0, 8, -29578318260090271286637620250683132587342508851200000⟩,
  ⟨0, 8, 3, 2, 1, 8, 8205029564351309474391033980098615456431498854400000⟩,
  ⟨0, 8, 4, 2, 2, 8, -23222390245393813811451354289608646751577282969600000⟩,
  ⟨0, 8, 5, 2, 3, 8, 81839540600806805833386751563946956983006920704000000⟩,
  ⟨0, 8, 6, 2, 4, 8, 6760456790088804327309382534995964974027767808000000⟩,
  ⟨0, 8, 7, 2, 5, 8, 770834798922221287142166893096513816802361344000000⟩,
  ⟨0, 8, 8, 2, 6, 8, 112213632416614199127212544287818124655329280000000⟩,
  ⟨0, 8, 3, 3, 0, 8, -84639548767034043032738331331965993102581170176000000⟩,
  ⟨0, 8, 4, 3, 1, 8, 51559027350016274652766547552729497771402749542400000⟩,
  ⟨0, 8, 5, 3, 2, 8, -222336277262475440363419946718221228991011880960000000⟩,
  ⟨0, 8, 6, 3, 3, 8, 10262998620346817924576323891949005763027927040000000⟩,
  ⟨0, 8, 7, 3, 4, 8, -3097134009920533828665350678329942092900886118400000⟩,
  ⟨0, 8, 8, 3, 5, 8, 1785405119169368770159543943941748718909259776000000⟩,
  ⟨0, 8, 4, 4, 0, 8, -86120545891703617804515911689718290701196512460800000⟩,
  ⟨0, 8, 5, 4, 1, 8, 61626770120480779596966521755244213544922644480000000⟩,
  ⟨0, 8, 6, 4, 2, 8, -31206646149205771505164031890625830218325032960000000⟩,
  ⟨0, 8, 7, 4, 3, 8, 10984880655792647923663897784541392236637375692800000⟩,
  ⟨0, 8, 8, 4, 4, 8, -2554368871543891671067249385432376985100746752000000⟩,
  ⟨0, 8, 5, 5, 0, 8, 705504847181998864521161885580236561179660517376000000⟩,
  ⟨0, 8, 6, 5, 1, 8, 48223396636737638020596900553599736272251781120000000⟩,
  ⟨0, 8, 7, 5, 2, 8, -21337075819521683846608881602476407533279064883200000⟩,
  ⟨0, 8, 8, 5, 3, 8, 3573138477027623393499962673696811670002728960000000⟩,
  ⟨0, 8, 6, 6, 0, 8, -70734300511088209629773191628555749100781305856000000⟩,
  ⟨0, 8, 7, 6, 1, 8, 58622924881775050129800510944364672122932848230400000⟩,
  ⟨0, 8, 8, 6, 2, 8, -12742335505472079413466754202644217109752787763200000⟩,
  ⟨0, 8, 7, 7, 0, 8, -198711915708511627287605934837563257151582896128000000⟩,
  ⟨0, 8, 8, 7, 1, 8, 23825369906328694703282142640793362639865511936000000⟩
]

def collectedFourData_10_0_9 : List CollectedFourTerm := [

]

def collectedFourData_10_0_10 : List CollectedFourTerm := [
  ⟨1, 1, 8, 0, 8, 2, 27981811730568543391180624264410516232456057651200000⟩,
  ⟨1, 1, 8, 1, 7, 2, 23382015251355737095982736573466118645952282624000000⟩,
  ⟨1, 1, 8, 2, 6, 2, 1272367917585757525726388663135698067726008320000000⟩,
  ⟨1, 1, 8, 3, 5, 2, 20244351284257484867575977112358377099723014144000000⟩,
  ⟨1, 1, 8, 4, 4, 2, -28963477358665183262743817889400144522628825088000000⟩,
  ⟨1, 1, 8, 5, 3, 2, 40515102000994099445315102287051857441576714240000000⟩,
  ⟨1, 1, 8, 6, 2, 2, -144482791824107325027745892586675137061868850380800000⟩,
  ⟨1, 1, 8, 7, 1, 2, 270151100544335217009799667402102850397283549184000000⟩
]

def collectedFourData_10_0_11 : List CollectedFourTerm := [
  ⟨1, 2, 7, 0, 7, 3, -7773053006520858325229943878607814197352857600000⟩,
  ⟨1, 2, 8, 0, 8, 3, 1048117323837294915583027709555447451958326067200000⟩,
  ⟨1, 2, 7, 1, 6, 3, -538006281465134450459217191993399048300553830400000⟩,
  ⟨1, 2, 8, 1, 7, 3, 875822319410475383833514080936982514650578944000000⟩,
  ⟨1, 2, 7, 2, 5, 3, 54564630691551293634026068081800825783975936000000⟩,
  ⟨1, 2, 8, 2, 6, 3, 47659203398168230896606208555183832479825920000000⟩,
  ⟨1, 2, 7, 3, 4, 3, -219235008188322729877632564258206911949281689600000⟩,
  ⟨1, 2, 8, 3, 5, 3, 758294548444055881996176532818050474588504064000000⟩,
  ⟨1, 2, 7, 4, 3, 3, 777580302565674404225938048761894328811598643200000⟩,
  ⟨1, 2, 8, 4, 4, 3, -1084887664547567497796685858027680323420028928000000⟩,
  ⟨1, 2, 7, 5, 2, 3, -1510375068377400629230886162383073878517533900800000⟩,
  ⟨1, 2, 8, 5, 3, 3, 1517577942885192832692634880249775489747517440000000⟩,
  ⟨1, 2, 7, 6, 1, 3, 4149706591743229964906321552646151397806021017600000⟩,
  ⟨1, 2, 8, 6, 2, 3, -5411905367864022160145668291136167136004459724800000⟩,
  ⟨1, 2, 7, 7, 0, 3, -14066103800458612417791517456519178996240351232000000⟩,
  ⟨1, 2, 8, 7, 1, 3, 10119074892670485430243329334080476261388386304000000⟩
]

def collectedFourData_10_0_12 : List CollectedFourTerm := [
  ⟨1, 3, 6, 0, 6, 4, 28523576974091326379835479701671278065150328832000000⟩,
  ⟨1, 3, 7, 0, 7, 4, -522841474861980573788147107882840785539825664000000⟩,
  ⟨1, 3, 8, 0, 8, 4, 35249933775298054303102747282954666324267106304000000⟩,
  ⟨1, 3, 6, 1, 5, 4, -17936756055610044524714608931571990965231026176000000⟩,
  ⟨1, 3, 7, 1, 6, 4, -36188097192990101061974130094807688427293638656000000⟩,
  ⟨1, 3, 8, 1, 7, 4, 29455365402337090505693062314457438798038958080000000⟩,
  ⟨1, 3, 6, 2, 4, 4, 6437753541938409415384449815486694015060934656000000⟩,
  ⟨1, 3, 7, 2, 5, 4, 3670199079066760661773304891204675755353047040000000⟩,
  ⟨1, 3, 8, 2, 6, 4, 1602858501964502739141965565899406672553574400000000⟩,
  ⟨1, 3, 6, 3, 3, 4, 9773105245774204887767620293756070881688289280000000⟩,
  ⟨1, 3, 7, 3, 4, 4, -14746477983155569646220698269441487084552454144000000⟩,
  ⟨1, 3, 8, 3, 5, 4, 25502710437950868886330839422189336537837076480000000⟩,
  ⟨1, 3, 6, 4, 2, 4, -29717029931113438794914168936067090094982430720000000⟩,
  ⟨1, 3, 7, 4, 3, 4, 52302645032267780033311546702126592428760629248000000⟩,
  ⟨1, 3, 8, 4, 4, 4, -36486581663329207046954467751530108998868008960000000⟩,
  ⟨1, 3, 6, 5, 1, 4, 45921503848319172681602500462469587287240867840000000⟩,
  ⟨1, 3, 7, 5, 2, 4, -101592865465182370273079008942712732275716390912000000⟩,
  ⟨1, 3, 8, 5, 3, 4, 51038677416098460303865465530263627031694540800000000⟩,
  ⟨1, 3, 6, 6, 0, 4, -67357873556619876605627245761314433536719060992000000⟩,
  ⟨1, 3, 7, 6, 1, 4, 279123108108408730791247710596940886000810328064000000⟩,
  ⟨1, 3, 8, 6, 2, 4, -182011404140287845207528669396954621813914075136000000⟩,
  ⟨1, 3, 7, 7, 0, 4, -946133063858421054270345664228790982408646164480000000⟩,
  ⟨1, 3, 8, 7, 1, 4, 340321366436347439652933759187411659839011553280000000⟩
]

def collectedFourData_10_0_13 : List CollectedFourTerm := [
  ⟨1, 4, 5, 0, 5, 5, 116492900353042042377065971862895856119479009280000000⟩,
  ⟨1, 4, 6, 0, 6, 5, 134655171213185305284364323493606798254680309760000000⟩,
  ⟨1, 4, 7, 0, 7, 5, -1234124815040613403339384941002894855645429760000000⟩,
  ⟨1, 4, 8, 0, 8, 5, 55469736165718215515008457019080054774421258240000000⟩,
  ⟨1, 4, 5, 1, 4, 5, 62340956813813538087929867023166625310939545600000000⟩,
  ⟨1, 4, 6, 1, 5, 5, -84676510238220295349914433346630645412716871680000000⟩,
  ⟨1, 4, 7, 1, 6, 5, -85419062760390498070313273034767814823551959040000000⟩,
  ⟨1, 4, 8, 1, 7, 5, 46351330982568564315631204768004600417275084800000000⟩,
  ⟨1, 4, 5, 2, 3, 5, 91977276600251470327334197620131305252202741760000000⟩,
  ⟨1, 4, 6, 2, 4, 5, 30391588201066520688485743125248618436577198080000000⟩,
  ⟨1, 4, 7, 2, 5, 5, 8663206683844632764746063922583604364417433600000000⟩,
  ⟨1, 4, 8, 2, 6, 5, 2522278163179258997627467064331629928382464000000000⟩,
  ⟨1, 4, 5, 3, 2, 5, -249877811164537530160000440465115449626355302400000000⟩,
  ⟨1, 4, 6, 3, 3, 5, 46137241530035301830635252571762981014496870400000000⟩,
  ⟨1, 4, 7, 3, 4, 5, -34807862972742371746973007175042200251620392960000000⟩,
  ⟨1, 4, 8, 3, 5, 5, 40131383750149511055425628075453863668010188800000000⟩,
  ⟨1, 4, 5, 4, 1, 5, 69260683035844086482212036132062183682159411200000000⟩,
  ⟨1, 4, 6, 4, 2, 5, -140289268662066517586951587850460317781432729600000000⟩,
  ⟨1, 4, 7, 4, 3, 5, 123456143458438674102786848654794407887052472320000000⟩,
  ⟨1, 4, 8, 4, 4, 5, -57415740731748089387226657437983526687971737600000000⟩,
  ⟨1, 4, 5, 5, 0, 5, 792898078309070308282554684256365634288814653440000000⟩,
  ⟨1, 4, 6, 5, 1, 5, 216787956457181176318534376548490070795170611200000000⟩,
  ⟨1, 4, 7, 5, 2, 5, -239801703441299118800128600349045635737012142080000000⟩,
  ⟨1, 4, 8, 5, 3, 5, 80315100407426056942239864247011620262248448000000000⟩,
  ⟨1, 4, 6, 6, 0, 5, -317985573988890697551786766421273375981237698560000000⟩,
  ⟨1, 4, 7, 6, 1, 5, 658847415000473721757844169969013171162982645760000000⟩,
  ⟨1, 4, 8, 6, 2, 5, -286415419420977663579925509712406266203246428160000000⟩,
  ⟨1, 4, 7, 7, 0, 5, -2233270213971294888258521305706963377337873203200000000⟩,
  ⟨1, 4, 8, 7, 1, 5, 535533953854110031725332292424888507156974796800000000⟩
]

def collectedFourData_10_0_14 : List CollectedFourTerm := [
  ⟨1, 5, 4, 0, 4, 6, 30083047848464350232685753945910838380995595468800000⟩,
  ⟨1, 5, 5, 0, 5, 6, -158230042873493793347491498548986141800277213184000000⟩,
  ⟨1, 5, 6, 0, 6, 6, -91449751227880601345909629244442863212758564864000000⟩,
  ⟨1, 5, 7, 0, 7, 6, 558762584968179188222589883883049870296088576000000⟩,
  ⟨1, 5, 8, 0, 8, 6, -18835866188161621404488568018012340884149895168000000⟩,
  ⟨1, 5, 4, 1, 3, 6, -17936756055610044524714608931571990965231026176000000⟩,
  ⟨1, 5, 5, 1, 4, 6, -84676510238220295349914433346630645412716871680000000⟩,
  ⟨1, 5, 6, 1, 5, 6, 57507229216400716978767528759491340757685501952000000⟩,
  ⟨1, 5, 7, 1, 6, 6, 38674351031491275358217049687972587473735778304000000⟩,
  ⟨1, 5, 8, 1, 7, 6, -15739528045032067658059062257578177132348047360000000⟩,
  ⟨1, 5, 4, 2, 2, 6, 11816599472640715037519781207973101506870535782400000⟩,
  ⟨1, 5, 5, 2, 3, 6, -124930947514733608083216915895077636335707619328000000⟩,
  ⟨1, 5, 6, 2, 4, 6, -20640151843909117864885113531218926194143526912000000⟩,
  ⟨1, 5, 7, 2, 5, 6, -3922355098758251841053552013677964398281359360000000⟩,
  ⟨1, 5, 8, 2, 6, 6, -856490354110042135167471944456050473487564800000000⟩,
  ⟨1, 5, 4, 3, 1, 6, -26235558396703646005264038552890449694687861145600000⟩,
  ⟨1, 5, 5, 3, 2, 6, 339404175309187222678927060006829975560488222720000000⟩,
  ⟨1, 5, 6, 3, 3, 6, -31333659318456429649077177624954681388758466560000000⟩,
  ⟨1, 5, 7, 3, 4, 6, 15759614631221596605566196713080946471674576896000000⟩,
  ⟨1, 5, 8, 3, 5, 6, -13627419679900193402979686620958242623360860160000000⟩,
  ⟨1, 5, 4, 4, 0, 6, 43822017734341013452041821389735190044286858035200000⟩,
  ⟨1, 5, 5, 4, 1, 6, -94075439902315837477779644591295356130935439360000000⟩,
  ⟨1, 5, 6, 4, 2, 6, 95276093769735927536348091424588632398694973440000000⟩,
  ⟨1, 5, 7, 4, 3, 6, -55896026891550212461025817045065576954757906432000000⟩,
  ⟨1, 5, 8, 4, 4, 6, 19496671235039486435012799193211806551449272320000000⟩,
  ⟨1, 5, 5, 5, 0, 6, -1076978052267018014428391960824762086636474335232000000⟩,
  ⟨1, 5, 6, 5, 1, 6, -147229434329133032061055345372195290500227399680000000⟩,
  ⟨1, 5, 7, 5, 2, 6, 108572664662142379082069329767418447921579819008000000⟩,
  ⟨1, 5, 8, 5, 3, 6, -27272610052506358765795319737706128000784793600000000⟩,
  ⟨1, 5, 6, 6, 0, 6, 215956813045820986405550826350598398738310365184000000⟩,
  ⟨1, 5, 7, 6, 1, 6, -298299880383778232393053210351049965160078770176000000⟩,
  ⟨1, 5, 8, 6, 2, 6, 97258124652374038916548668690368411959465869312000000⟩,
  ⟨1, 5, 7, 7, 0, 6, 1011135844999578675946049119779193174431702712320000000⟩,
  ⟨1, 5, 8, 7, 1, 6, -181851340772147491370934750117206657517496565760000000⟩
]

def collectedFourData_10_0_15 : List CollectedFourTerm := [
  ⟨1, 6, 3, 0, 3, 7, 4994815477363109997725360107485417067348230144000000⟩,
  ⟨1, 6, 4, 0, 4, 7, 60693709387941708654352856660543805668335602892800000⟩,
  ⟨1, 6, 5, 0, 5, 7, -159617607347847614827023474903451960542077386752000000⟩,
  ⟨1, 6, 6, 0, 6, 7, -61501133490899296807761636775927244613671190528000000⟩,
  ⟨1, 6, 7, 0, 7, 7, 281831266896091201179936275607456185805963264000000⟩,
  ⟨1, 6, 8, 0, 8, 7, -7600417313120064747058480311711685806382487961600000⟩,
  ⟨1, 6, 3, 1, 2, 7, -538006281465134450459217191993399048300553830400000⟩,
  ⟨1, 6, 4, 1, 3, 7, -36188097192990101061974130094807688427293638656000000⟩,
  ⟨1, 6, 5, 1, 4, 7, -85419062760390498070313273034767814823551959040000000⟩,
  ⟨1, 6, 6, 1, 5, 7, 38674351031491275358217049687972587473735778304000000⟩,
  ⟨1, 6, 7, 1, 6, 7, 19506748735171769335120340570185237826220589056000000⟩,
  ⟨1, 6, 8, 1, 7, 7, -6351020986175104812776030446829999004196012032000000⟩,
  ⟨1, 6, 3, 2, 1, 7, -4211701633808130219476472894797105323144170700800000⟩,
  ⟨1, 6, 4, 2, 2, 7, 23840445222134345144072634299752326694493906534400000⟩,
  ⟨1, 6, 5, 2, 3, 7, -126026502703689732742630787528682947558856720384000000⟩,
  ⟨1, 6, 6, 2, 4, 7, -13880767490132677136618982262998388828457140224000000⟩,
  ⟨1, 6, 7, 2, 5, 7, -1978375675891639301903217412859215704269783040000000⟩,
  ⟨1, 6, 8, 2, 6, 7, -345600465137602665604748276458958169581813760000000⟩,
  ⟨1, 6, 3, 3, 0, 7, 43446098887406417950183210289574087036116140032000000⟩,
  ⟨1, 6, 4, 3, 1, 7, -52931251014886407698395389496876008102128359833600000⟩,
  ⟨1, 6, 5, 3, 2, 7, 342380507537592855757244793574871517020458844160000000⟩,
  ⟨1, 6, 6, 3, 3, 7, -21072288755611633398912580469648212739877765120000000⟩,
  ⟨1, 6, 7, 3, 4, 7, 7948907598321563344178634278163912137317023744000000⟩,
  ⟨1, 6, 8, 3, 5, 7, -5498768967331219925181810008137354808647483392000000⟩,
  ⟨1, 6, 4, 4, 0, 7, 88412611067834073181480565813921858337627124531200000⟩,
  ⟨1, 6, 5, 4, 1, 7, -94900414325295838706636832652306611353765806080000000⟩,
  ⟨1, 6, 6, 4, 2, 7, 64074398046449090175686064253057394298197114880000000⟩,
  ⟨1, 6, 7, 4, 3, 7, -28193097564327264700287240413521490257744232448000000⟩,
  ⟨1, 6, 8, 4, 4, 7, 7867057247207312927537117184387642626024669184000000⟩,
  ⟨1, 6, 5, 5, 0, 7, -1086422380650214203566469912169971014726420791296000000⟩,
  ⟨1, 6, 6, 5, 1, 7, -99013687548501947271868757264271006061937295360000000⟩,
  ⟨1, 6, 7, 5, 2, 7, 54762384696460379495998809003114962932268531712000000⟩,
  ⟨1, 6, 8, 5, 3, 7, -11004708546258390460300990067257403150507704320000000⟩,
  ⟨1, 6, 6, 6, 0, 7, 145233733378938000017669167894231177525532295168000000⟩,
  ⟨1, 6, 7, 6, 1, 7, -150457878650375946450440248312259384659792625664000000⟩,
  ⟨1, 6, 8, 6, 2, 7, 39244403579065725758492891721712966308498663014400000⟩,
  ⟨1, 6, 7, 7, 0, 7, 510001392123471581253457063077898396820286996480000000⟩,
  ⟨1, 6, 8, 7, 1, 7, -73378418863869824053418514419628913156908122112000000⟩
]

def collectedFourData_10_0_16 : List CollectedFourTerm := [
  ⟨1, 7, 2, 0, 2, 8, -4434694610774247672868520275806132377562906624000000⟩,
  ⟨1, 7, 3, 0, 3, 8, -8131077697640216670583869829869495201394851840000000⟩,
  ⟨1, 7, 4, 0, 4, 8, -49401751579007623540108694273610904328107720704000000⟩,
  ⟨1, 7, 5, 0, 5, 8, 86614021621605653256944328342251864957638410240000000⟩,
  ⟨1, 7, 6, 0, 6, 8, 25029477924349919932915122328325340700103147520000000⟩,
  ⟨1, 7, 7, 0, 7, 8, -91758822288517623610640648695782426707755008000000⟩,
  ⟨1, 7, 8, 0, 8, 8, 2062124349656479812596750064392856859570077696000000⟩,
  ⟨1, 7, 2, 1, 1, 8, 23382015251355737095982736573466118645952282624000000⟩,
  ⟨1, 7, 3, 1, 2, 8, 875822319410475383833514080936982514650578944000000⟩,
  ⟨1, 7, 4, 1, 3, 8, 29455365402337090505693062314457438798038958080000000⟩,
  ⟨1, 7, 5, 1, 4, 8, 46351330982568564315631204768004600417275084800000000⟩,
  ⟨1, 7, 6, 1, 5, 8, -15739528045032067658059062257578177132348047360000000⟩,
  ⟨1, 7, 7, 1, 6, 8, -6351020986175104812776030446829999004196012032000000⟩,
  ⟨1, 7, 8, 1, 7, 8, 1723141569892914184266141340264068030576721920000000⟩,
  ⟨1, 7, 2, 2, 0, 8, -24716079692272036065830930680056831285210906624000000⟩,
  ⟨1, 7, 3, 2, 1, 8, 6856243915110816352971300611619374269923852288000000⟩,
  ⟨1, 7, 4, 2, 2, 8, -19404972348432718295733456750921948205984776192000000⟩,
  ⟨1, 7, 5, 2, 3, 8, 68386329123983824400500782519183499130390446080000000⟩,
  ⟨1, 7, 6, 2, 4, 8, 5649137564573846622164985700424203630710620160000000⟩,
  ⟨1, 7, 7, 2, 5, 8, 644120945356274839213304152555873876448378880000000⟩,
  ⟨1, 7, 8, 2, 6, 8, 93767368955204850260541662592939385788825600000000⟩,
  ⟨1, 7, 3, 3, 0, 8, -70726057311602347595474236058119207258706411520000000⟩,
  ⟨1, 7, 4, 3, 1, 8, 43083484924106923689452983572904549347175170048000000⟩,
  ⟨1, 7, 5, 3, 2, 8, -185787477806578405404929249675468866227221299200000000⟩,
  ⟨1, 7, 6, 3, 3, 8, 8575913260235362399087790786623504384838860800000000⟩,
  ⟨1, 7, 7, 3, 4, 8, -2588010931984891752639561162425755882192109568000000⟩,
  ⟨1, 7, 8, 3, 5, 8, 1491910892984146734151551414491091377345003520000000⟩,
  ⟨1, 7, 4, 4, 0, 8, -71963600387428567312828278391106045905119215616000000⟩,
  ⟨1, 7, 5, 4, 1, 8, 51496239511707906755366490008428457921976729600000000⟩,
  ⟨1, 7, 6, 4, 2, 8, -26076734531354999487950327615014213201900339200000000⟩,
  ⟨1, 7, 7, 4, 3, 8, 9179128553262107589530151597619980000093536256000000⟩,
  ⟨1, 7, 8, 4, 4, 8, -2134468364204596156471437440490281089672151040000000⟩,
  ⟨1, 7, 5, 5, 0, 8, 589530272576804394361576404587312682758590955520000000⟩,
  ⟨1, 7, 6, 5, 1, 8, 40296182623535444745159548236187746961876582400000000⟩,
  ⟨1, 7, 7, 5, 2, 8, -17829575762829022406116326513573477896121483264000000⟩,
  ⟨1, 7, 8, 5, 3, 8, 2985767296611296404300798112054294210622259200000000⟩,
  ⟨1, 7, 6, 6, 0, 8, -59106626449689136871941704888519490180082565120000000⟩,
  ⟨1, 7, 7, 6, 1, 8, 48986182055085079120255818075070228903187447808000000⟩,
  ⟨1, 7, 8, 6, 2, 8, -10647683788157136813813424959298252279186980864000000⟩,
  ⟨1, 7, 7, 7, 0, 8, -166046612294468819783349687747983526848951746560000000⟩,
  ⟨1, 7, 8, 7, 1, 8, 19908831060798882537063982008391579680343326720000000⟩
]

def collectedFourData_10_0_17 : List CollectedFourTerm := [
  ⟨2, 0, 8, 0, 8, 2, -29578318260090271286637620250683132587342508851200000⟩,
  ⟨2, 0, 8, 1, 7, 2, -24716079692272036065830930680056831285210906624000000⟩,
  ⟨2, 0, 8, 2, 6, 2, -1344963062887249844538052762290388713414328320000000⟩,
  ⟨2, 0, 8, 3, 5, 2, -21399395829709151351066957494366666986193158144000000⟩,
  ⟨2, 0, 8, 4, 4, 2, 30615992970091754999659202418367927401565913088000000⟩,
  ⟨2, 0, 8, 5, 3, 2, -42826697315537789319428807733332507200050954240000000⟩,
  ⟨2, 0, 8, 6, 2, 2, 152726279514317335831257094454548223896658431180800000⟩,
  ⟨2, 0, 8, 7, 1, 2, -285564612726083741074268783644334054525248733184000000⟩
]

def collectedFourData_10_0_18 : List CollectedFourTerm := [
  ⟨2, 1, 7, 0, 7, 3, -60850181819601436601240711923365347731911475200000⟩,
  ⟨2, 1, 8, 0, 8, 3, 8205029564351309474391033980098615456431498854400000⟩,
  ⟨2, 1, 7, 1, 6, 3, -4211701633808130219476472894797105323144170700800000⟩,
  ⟨2, 1, 8, 1, 7, 3, 6856243915110816352971300611619374269923852288000000⟩,
  ⟨2, 1, 7, 2, 5, 3, 427151042931896856536693103967434464896745472000000⟩,
  ⟨2, 1, 8, 2, 6, 3, 373092939122249300597573088402944101806243840000000⟩,
  ⟨2, 1, 7, 3, 4, 3, -1716248441672768077724073431465299451523052339200000⟩,
  ⟨2, 1, 8, 3, 5, 3, 5936195354248103180214935432739442589096214528000000⟩,
  ⟨2, 1, 7, 4, 3, 3, 6087170993272322379802582817302518816284501606400000⟩,
  ⟨2, 1, 8, 4, 4, 3, -8492880672006402391641900491423302838340550656000000⟩,
  ⟨2, 1, 7, 5, 2, 3, -11823745116552892881131418525043359631971817881600000⟩,
  ⟨2, 1, 8, 5, 3, 3, 11880131741352085501267644045828820967494778880000000⟩,
  ⟨2, 1, 7, 6, 1, 3, 32485356833890328986207051421868731442088063795200000⟩,
  ⟨2, 1, 8, 6, 2, 3, -42366290999011349171834536702384017208099051929600000⟩,
  ⟨2, 1, 7, 7, 0, 3, -110114387877356941725709279837822597523690225664000000⟩,
  ⟨2, 1, 8, 7, 1, 3, 79215662951044951790951932505833458588092203008000000⟩
]

def collectedFourData_10_0_19 : List CollectedFourTerm := [
  ⟨2, 2, 6, 0, 6, 4, -18791117166610258140690067417285170214319475916800000⟩,
  ⟨2, 2, 7, 0, 7, 4, 344444016352467872710656404772729579806235033600000⟩,
  ⟨2, 2, 8, 0, 8, 4, -23222390245393813811451354289608646751577282969600000⟩,
  ⟨2, 2, 6, 1, 5, 4, 11816599472640715037519781207973101506870535782400000⟩,
  ⟨2, 2, 7, 1, 6, 4, 23840445222134345144072634299752326694493906534400000⟩,
  ⟨2, 2, 8, 1, 7, 4, -19404972348432718295733456750921948205984776192000000⟩,
  ⟨2, 2, 6, 2, 4, 4, -4241143430440271867110948952613095005963576934400000⟩,
  ⟨2, 2, 7, 2, 5, 4, -2417899444455130362863698107789189021010231296000000⟩,
  ⟨2, 2, 8, 2, 6, 4, -1055951080023051158153137434009406171313602560000000⟩,
  ⟨2, 2, 6, 3, 3, 4, -6438447952084273093572865333325590199713923072000000⟩,
  ⟨2, 2, 7, 3, 4, 4, 9714868364091018302908841262764354356029004185600000⟩,
  ⟨2, 2, 8, 3, 5, 4, -16800993099181096170031101847611886698183524352000000⟩,
  ⟨2, 2, 6, 4, 2, 4, 19577354964506727076569208384123361083867004928000000⟩,
  ⟨2, 2, 7, 4, 3, 4, -34456587678946939384273416673841202866878100275200000⟩,
  ⟨2, 2, 8, 4, 4, 4, 24037084537731067418492822469613293242998063104000000⟩,
  ⟨2, 2, 6, 5, 1, 4, -30252740042545077900234201345294561173324169216000000⟩,
  ⟨2, 2, 7, 5, 2, 4, 66928612774686234856690687815786946225765141708800000⟩,
  ⟨2, 2, 8, 5, 3, 4, -33623895355967507201557924622620025685981265920000000⟩,
  ⟨2, 2, 6, 6, 0, 4, 44374858568609983751104585006888452061754346700800000⟩,
  ⟨2, 2, 7, 6, 1, 4, -183884196331256976141048119312338736224323344793600000⟩,
  ⟨2, 2, 8, 6, 2, 4, 119907738919492839678993346702053695641623094886400000⟩,
  ⟨2, 2, 7, 7, 0, 4, 623305319466648574921887379396415873254321815552000000⟩,
  ⟨2, 2, 8, 7, 1, 4, -224201146890344883601711324840962382820039196672000000⟩
]

def collectedFourData_10_0_20 : List CollectedFourTerm := [
  ⟨2, 3, 5, 0, 5, 5, 171872558031754686900901530461199048171520524288000000⟩,
  ⟨2, 3, 6, 0, 6, 5, 198669006080847355374383440139235803402229252096000000⟩,
  ⟨2, 3, 7, 0, 7, 5, -1820816446742003928717752629012211623155204096000000⟩,
  ⟨2, 3, 8, 0, 8, 5, 81839540600806805833386751563946956983006920704000000⟩,
  ⟨2, 3, 5, 1, 4, 5, 91977276600251470327334197620131305252202741760000000⟩,
  ⟨2, 3, 6, 1, 5, 5, -124930947514733608083216915895077636335707619328000000⟩,
  ⟨2, 3, 7, 1, 6, 5, -126026502703689732742630787528682947558856720384000000⟩,
  ⟨2, 3, 8, 1, 7, 5, 68386329123983824400500782519183499130390446080000000⟩,
  ⟨2, 3, 5, 2, 3, 5, 135702431325607052087575967062419998628743479296000000⟩,
  ⟨2, 3, 6, 2, 4, 5, 44839470825559139203107686647386220520452128768000000⟩,
  ⟨2, 3, 7, 2, 5, 5, 12781615780856378229903533329643902478120386560000000⟩,
  ⟨2, 3, 8, 2, 6, 5, 3721346096281088234497468131750827717453414400000000⟩,
  ⟨2, 3, 5, 3, 2, 5, -368667433552342779288553708295859907960284119040000000⟩,
  ⟨2, 3, 6, 3, 3, 5, 68070463506911917834968359828915314505904291840000000⟩,
  ⟨2, 3, 7, 3, 4, 5, -51355202167801497237345199983237472758389538816000000⟩,
  ⟨2, 3, 8, 3, 5, 5, 59209475955948856572952023048924919379766804480000000⟩,
  ⟨2, 3, 5, 4, 1, 5, 102186577279138232382127739749180536281125355520000000⟩,
  ⟨2, 3, 6, 4, 2, 5, -206981501845007546383580657847361895552683868160000000⟩,
  ⟨2, 3, 7, 4, 3, 5, 182146063121717414969124644509163802487079043072000000⟩,
  ⟨2, 3, 8, 4, 4, 5, -84710657910886681718378570284268784748289064960000000⟩,
  ⟨2, 3, 5, 5, 0, 5, 1169834561286067013077108055358966182425997082624000000⟩,
  ⟨2, 3, 6, 5, 1, 5, 319846965041242463173578204583082574785040875520000000⟩,
  ⟨2, 3, 7, 5, 2, 5, -353801236521037756511227167021098161233532551168000000⟩,
  ⟨2, 3, 8, 5, 3, 5, 118496163403670197303787950457229370521865420800000000⟩,
  ⟨2, 3, 6, 6, 0, 5, -469153002912930365506705502546261794501297176576000000⟩,
  ⟨2, 3, 7, 6, 1, 5, 972057440629972633536294683645898892010581917696000000⟩,
  ⟨2, 3, 8, 6, 2, 5, -422574686066144045190821041979964696175350644736000000⟩,
  ⟨2, 3, 7, 7, 0, 5, -3294946415516447572085206481783708622797899038720000000⟩,
  ⟨2, 3, 8, 7, 1, 5, 790121889684429843660130369932776530808961761280000000⟩
]

def collectedFourData_10_0_21 : List CollectedFourTerm := [
  ⟨2, 4, 4, 0, 4, 6, -10797228174276311611318570218432419743067327692800000⟩,
  ⟨2, 4, 5, 0, 5, 6, 56790983597689120525678017731000227689350037504000000⟩,
  ⟨2, 4, 6, 0, 6, 6, 32822599474030227576210136790771128737762115584000000⟩,
  ⟨2, 4, 7, 0, 7, 6, -200547735573204458344897189130727843541549056000000⟩,
  ⟨2, 4, 8, 0, 8, 6, 6760456790088804327309382534995964974027767808000000⟩,
  ⟨2, 4, 4, 1, 3, 6, 6437753541938409415384449815486694015060934656000000⟩,
  ⟨2, 4, 5, 1, 4, 6, 30391588201066520688485743125248618436577198080000000⟩,
  ⟨2, 4, 6, 1, 5, 6, -20640151843909117864885113531218926194143526912000000⟩,
  ⟨2, 4, 7, 1, 6, 6, -13880767490132677136618982262998388828457140224000000⟩,
  ⟨2, 4, 8, 1, 7, 6, 5649137564573846622164985700424203630710620160000000⟩,
  ⟨2, 4, 4, 2, 2, 6, -4241143430440271867110948952613095005963576934400000⟩,
  ⟨2, 4, 5, 2, 3, 6, 44839470825559139203107686647386220520452128768000000⟩,
  ⟨2, 4, 6, 2, 4, 6, 7408040240236922888491471842047095535327772672000000⟩,
  ⟨2, 4, 7, 2, 5, 6, 1407788306396315200351532924830972557561692160000000⟩,
  ⟨2, 4, 8, 2, 6, 6, 307406411377459895642954492373636123249868800000000⟩,
  ⟨2, 4, 4, 3, 1, 6, 9416310199540510299652972327792972497486977433600000⟩,
  ⟨2, 4, 5, 3, 2, 6, -121816923025053157498335572375115102907866808320000000⟩,
  ⟨2, 4, 6, 3, 3, 6, 11246090186758896175865577696720661610087055360000000⟩,
  ⟨2, 4, 7, 3, 4, 6, -5656346922329852134796878559394564398672510976000000⟩,
  ⟨2, 4, 8, 3, 5, 6, 4891072222857127088920165520751041283316776960000000⟩,
  ⟨2, 4, 4, 4, 0, 6, -15728337331984005991055420448013529654169383731200000⟩,
  ⟨2, 4, 5, 4, 1, 6, 33764995998321816082029368865433671591694172160000000⟩,
  ⟨2, 4, 6, 4, 2, 6, -34195927525943734603122843577692825370377584640000000⟩,
  ⟨2, 4, 7, 4, 3, 6, 20061868711695724068583319813132458692855201792000000⟩,
  ⟨2, 4, 8, 4, 4, 6, -6997628997698675100334974393680606844074065920000000⟩,
  ⟨2, 4, 5, 5, 0, 6, 386542541420325765998393937601673078482604654592000000⟩,
  ⟨2, 4, 6, 5, 1, 6, 52842710766170824060601315015974696549173166080000000⟩,
  ⟨2, 4, 7, 5, 2, 6, -38968253474562065157341042830334498515974094848000000⟩,
  ⟨2, 4, 8, 5, 3, 6, 9788522596788834262243051765570607672564121600000000⟩,
  ⟨2, 4, 6, 6, 0, 6, -77509931772564347766294561898555488393184149504000000⟩,
  ⟨2, 4, 7, 6, 1, 6, 107064014560193468329515097175255599203961798656000000⟩,
  ⟨2, 4, 8, 6, 2, 6, -34907306233184609810305794034566957235880067072000000⟩,
  ⟨2, 4, 7, 7, 0, 6, -362910848948685910273947203148257875661338705920000000⟩,
  ⟨2, 4, 8, 7, 1, 6, 65268999005869804792371487387610603604997570560000000⟩
]

def collectedFourData_10_0_22 : List CollectedFourTerm := [
  ⟨2, 5, 3, 0, 3, 7, -506574497889806841894974268430666446101544960000000⟩,
  ⟨2, 5, 4, 0, 4, 7, -6155559799477910021597453823963560747049418752000000⟩,
  ⟨2, 5, 5, 0, 5, 7, 16188427713308711017376548800599692628648263680000000⟩,
  ⟨2, 5, 6, 0, 6, 7, 6237448802463822168954411956308722578903531520000000⟩,
  ⟨2, 5, 7, 0, 7, 7, -28583344703037293567235314435772376688885760000000⟩,
  ⟨2, 5, 8, 0, 8, 7, 770834798922221287142166893096513816802361344000000⟩,
  ⟨2, 5, 3, 1, 2, 7, 54564630691551293634026068081800825783975936000000⟩,
  ⟨2, 5, 4, 1, 3, 7, 3670199079066760661773304891204675755353047040000000⟩,
  ⟨2, 5, 5, 1, 4, 7, 8663206683844632764746063922583604364417433600000000⟩,
  ⟨2, 5, 6, 1, 5, 7, -3922355098758251841053552013677964398281359360000000⟩,
  ⟨2, 5, 7, 1, 6, 7, -1978375675891639301903217412859215704269783040000000⟩,
  ⟨2, 5, 8, 1, 7, 7, 644120945356274839213304152555873876448378880000000⟩,
  ⟨2, 5, 3, 2, 1, 7, 427151042931896856536693103967434464896745472000000⟩,
  ⟨2, 5, 4, 2, 2, 7, -2417899444455130362863698107789189021010231296000000⟩,
  ⟨2, 5, 5, 2, 3, 7, 12781615780856378229903533329643902478120386560000000⟩,
  ⟨2, 5, 6, 2, 4, 7, 1407788306396315200351532924830972557561692160000000⟩,
  ⟨2, 5, 7, 2, 5, 7, 200646984697280237877544011798610940893593600000000⟩,
  ⟨2, 5, 8, 2, 6, 7, 35050820774262100154154428360100663420518400000000⟩,
  ⟨2, 5, 3, 3, 0, 7, -4406306064539094096803540418982050794443898880000000⟩,
  ⟨2, 5, 4, 3, 1, 7, 5368290786129501444226673943845023100461645824000000⟩,
  ⟨2, 5, 5, 3, 2, 7, -34724252473221966113059136977801396066084454400000000⟩,
  ⟨2, 5, 6, 3, 3, 7, 2137152842610799065903741575300039689686220800000000⟩,
  ⟨2, 5, 7, 3, 4, 7, -806178705427977277410485988282556415433768960000000⟩,
  ⟨2, 5, 8, 3, 5, 7, 557685492339432669951182071684862475270881280000000⟩,
  ⟨2, 5, 4, 4, 0, 7, -8966812540282133320982783665976546634296721408000000⟩,
  ⟨2, 5, 5, 4, 1, 7, 9624805952141184287223816441894261014868787200000000⟩,
  ⟨2, 5, 6, 4, 2, 7, -6498429454516548411712280422319984569692979200000000⟩,
  ⟨2, 5, 7, 4, 3, 7, 2859345717040822597153590078414552322875064320000000⟩,
  ⟨2, 5, 8, 4, 4, 7, -797877437702328415873932985578854313162178560000000⟩,
  ⟨2, 5, 5, 5, 0, 7, 110185025746872365622729336722080137652878704640000000⟩,
  ⟨2, 5, 6, 5, 1, 7, 10041974379518054891013698029273878188418662400000000⟩,
  ⟨2, 5, 7, 5, 2, 7, -5554004478560468841806837749287905136822190080000000⟩,
  ⟨2, 5, 8, 5, 3, 7, 1116098228555089405907490207387570550918348800000000⟩,
  ⟨2, 5, 6, 6, 0, 7, -14729614316390716823020330564873774867540869120000000⟩,
  ⟨2, 5, 7, 6, 1, 7, 15259447456328690687081659235446606119315701760000000⟩,
  ⟨2, 5, 8, 6, 2, 7, -3980169863761499491447938773268090638875754496000000⟩,
  ⟨2, 5, 7, 7, 0, 7, -51724373064216095618740734039247527013987123200000000⟩,
  ⟨2, 5, 8, 7, 1, 7, 7442043827320051012293959270617887161796526080000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1002. -/
namespace LaughlinFock
def collectedFourData_10_0_23 : List CollectedFourTerm := [
  ⟨2, 6, 2, 0, 2, 8, -241320651209157159901267471087321464774328320000000⟩,
  ⟨2, 6, 3, 0, 3, 8, -442464958073903065173349047047192367543091200000000⟩,
  ⟨2, 6, 4, 0, 4, 8, -2688271438794235212410669165122511079965982720000000⟩,
  ⟨2, 6, 5, 0, 5, 8, 4713233702899935301991929873921887450641203200000000⟩,
  ⟨2, 6, 6, 0, 6, 8, 1362017104279207034976001952630388255463833600000000⟩,
  ⟨2, 6, 7, 0, 7, 8, -4993195855031926798113619690670066698813440000000⟩,
  ⟨2, 6, 8, 0, 8, 8, 112213632416614199127212544287818124655329280000000⟩,
  ⟨2, 6, 2, 1, 1, 8, 1272367917585757525726388663135698067726008320000000⟩,
  ⟨2, 6, 3, 1, 2, 8, 47659203398168230896606208555183832479825920000000⟩,
  ⟨2, 6, 4, 1, 3, 8, 1602858501964502739141965565899406672553574400000000⟩,
  ⟨2, 6, 5, 1, 4, 8, 2522278163179258997627467064331629928382464000000000⟩,
  ⟨2, 6, 6, 1, 5, 8, -856490354110042135167471944456050473487564800000000⟩,
  ⟨2, 6, 7, 1, 6, 8, -345600465137602665604748276458958169581813760000000⟩,
  ⟨2, 6, 8, 1, 7, 8, 93767368955204850260541662592939385788825600000000⟩,
  ⟨2, 6, 2, 2, 0, 8, -1344963062887249844538052762290388713414328320000000⟩,
  ⟨2, 6, 3, 2, 1, 8, 373092939122249300597573088402944101806243840000000⟩,
  ⟨2, 6, 4, 2, 2, 8, -1055951080023051158153137434009406171313602560000000⟩,
  ⟨2, 6, 5, 2, 3, 8, 3721346096281088234497468131750827717453414400000000⟩,
  ⟨2, 6, 6, 2, 4, 8, 307406411377459895642954492373636123249868800000000⟩,
  ⟨2, 6, 7, 2, 5, 8, 35050820774262100154154428360100663420518400000000⟩,
  ⟨2, 6, 8, 2, 6, 8, 5102493976352691126638739218721310507008000000000⟩,
  ⟨2, 6, 3, 3, 0, 8, -3848665963700311933572783138894984232147353600000000⟩,
  ⟨2, 6, 4, 3, 1, 8, 2344453350403355105668209897758922472308080640000000⟩,
  ⟨2, 6, 5, 3, 2, 8, -10109908137048192644336126202396873804742656000000000⟩,
  ⟨2, 6, 6, 3, 3, 8, 466671361686374276099065227102955864326144000000000⟩,
  ⟨2, 6, 7, 3, 4, 8, -140830550524419107683849748547161152542474240000000⟩,
  ⟨2, 6, 8, 3, 5, 8, 81184600032269748585812494456489554581913600000000⟩,
  ⟨2, 6, 4, 4, 0, 8, -3916008752137693578399073594983807124903034880000000⟩,
  ⟨2, 6, 5, 4, 1, 8, 2802246184798382045642543346390472461385728000000000⟩,
  ⟨2, 6, 6, 4, 2, 8, -1419005165141741896792067141538534817529856000000000⟩,
  ⟨2, 6, 7, 4, 3, 8, 499496239182757758129496444229320991393710080000000⟩,
  ⟨2, 6, 8, 4, 4, 8, -116150341983812150402860171561589546365747200000000⟩,
  ⟨2, 6, 5, 5, 0, 8, 32080186297407377020945432838794452825381273600000000⟩,
  ⟨2, 6, 6, 5, 1, 8, 2192778056989349995429955949078431957778432000000000⟩,
  ⟨2, 6, 7, 5, 2, 8, -970223479067865610413402658410883605615083520000000⟩,
  ⟨2, 6, 8, 5, 3, 8, 162475067984770840136558665724246366355456000000000⟩,
  ⟨2, 6, 6, 6, 0, 8, -3216376963356469544625650659061511415765401600000000⟩,
  ⟨2, 6, 7, 6, 1, 8, 2665657591181815489228883866241953609222717440000000⟩,
  ⟨2, 6, 8, 6, 2, 8, -579409905562507014624959026979737454531051520000000⟩,
  ⟨2, 6, 7, 7, 0, 8, -9035678919721555246320793739633831560662220800000000⟩,
  ⟨2, 6, 8, 7, 1, 8, 1083369318088463661347922091170549275924889600000000⟩
]

def collectedFourData_10_0_24 : List CollectedFourTerm := [
  ⟨3, 0, 7, 0, 7, 3, 627704250327126019870408039637328061695787008000000⟩,
  ⟨3, 0, 8, 0, 8, 3, -84639548767034043032738331331965993102581170176000000⟩,
  ⟨3, 0, 7, 1, 6, 3, 43446098887406417950183210289574087036116140032000000⟩,
  ⟨3, 0, 8, 1, 7, 3, -70726057311602347595474236058119207258706411520000000⟩,
  ⟨3, 0, 7, 2, 5, 3, -4406306064539094096803540418982050794443898880000000⟩,
  ⟨3, 0, 8, 2, 6, 3, -3848665963700311933572783138894984232147353600000000⟩,
  ⟨3, 0, 7, 3, 4, 3, 17704079252369263528416883099672985716358381568000000⟩,
  ⟨3, 0, 8, 3, 5, 3, -61235232881972677113178678794242059819674501120000000⟩,
  ⟨3, 0, 7, 4, 3, 3, -62792632506386437441556306954498768597214560256000000⟩,
  ⟨3, 0, 8, 4, 4, 3, 87608896735001321308390624836450169764697866240000000⟩,
  ⟨3, 0, 7, 5, 2, 3, 121968658802825301638772061248054184640998539264000000⟩,
  ⟨3, 0, 8, 5, 3, 3, -122550318922641948799727202068225671577154355200000000⟩,
  ⟨3, 0, 7, 6, 1, 3, -335104940499253706054206042786986520085746679808000000⟩,
  ⟨3, 0, 8, 6, 2, 3, 437032398843364227482985865566715692573926621184000000⟩,
  ⟨3, 0, 7, 7, 0, 3, 1135892568040307586505083267333366291349697986560000000⟩,
  ⟨3, 0, 8, 7, 1, 3, -817154638490078560012185014055785639440621240320000000⟩
]

def collectedFourData_10_0_25 : List CollectedFourTerm := [
  ⟨3, 1, 6, 0, 6, 4, 41720585766264582135687284029334926941475779379200000⟩,
  ⟨3, 1, 7, 0, 7, 4, -764744639634539781825427381608479044432979558400000⟩,
  ⟨3, 1, 8, 0, 8, 4, 51559027350016274652766547552729497771402749542400000⟩,
  ⟨3, 1, 6, 1, 5, 4, -26235558396703646005264038552890449694687861145600000⟩,
  ⟨3, 1, 7, 1, 6, 4, -52931251014886407698395389496876008102128359833600000⟩,
  ⟨3, 1, 8, 1, 7, 4, 43083484924106923689452983572904549347175170048000000⟩,
  ⟨3, 1, 6, 2, 4, 4, 9416310199540510299652972327792972497486977433600000⟩,
  ⟨3, 1, 7, 2, 5, 4, 5368290786129501444226673943845023100461645824000000⟩,
  ⟨3, 1, 8, 2, 6, 4, 2344453350403355105668209897758922472308080640000000⟩,
  ⟨3, 1, 6, 3, 3, 4, 14294829711554518235959167751416406198104096768000000⟩,
  ⟨3, 1, 7, 3, 4, 4, -21569233760737811359647334380916226009298527846400000⟩,
  ⟨3, 1, 8, 3, 5, 4, 37302054334391053386160340668543207585861337088000000⟩,
  ⟨3, 1, 6, 4, 2, 4, -43466213830257749159451298280538220759175135232000000⟩,
  ⟨3, 1, 7, 4, 3, 4, 76501519772687451055667031504020937622902590668800000⟩,
  ⟨3, 1, 8, 4, 4, 4, -53367835351976810108518040556369915987703627776000000⟩,
  ⟨3, 1, 6, 5, 1, 4, 67168014781592199360472209671686831665057890304000000⟩,
  ⟨3, 1, 7, 5, 2, 4, -148596855882790144559161164692107273986204971827200000⟩,
  ⟨3, 1, 8, 5, 3, 4, 74652752018766818459784295820902179023597076480000000⟩,
  ⟨3, 1, 6, 6, 0, 4, -98522353746332313669161834086819879556727649075200000⟩,
  ⟨3, 1, 7, 6, 1, 4, 408265049708205018964927805518952007326203536998400000⟩,
  ⟨3, 1, 8, 6, 2, 4, -266222655165956197952426364614676540524018112921600000⟩,
  ⟨3, 1, 7, 7, 0, 4, -1383880628746473554917974028076162074301209509888000000⟩,
  ⟨3, 1, 8, 7, 1, 4, 497777917874632473315159145748077066793326215168000000⟩
]

def collectedFourData_10_0_26 : List CollectedFourTerm := [
  ⟨3, 2, 5, 0, 5, 5, -466932053086114057614764352063960892874812293120000000⟩,
  ⟨3, 2, 6, 0, 6, 5, -539730879415716549548888334356388751682347991040000000⟩,
  ⟨3, 2, 7, 0, 7, 5, 4946674277188141083569865273588892096832471040000000⟩,
  ⟨3, 2, 8, 0, 8, 5, -222336277262475440363419946718221228991011880960000000⟩,
  ⟨3, 2, 5, 1, 4, 5, -249877811164537530160000440465115449626355302400000000⟩,
  ⟨3, 2, 6, 1, 5, 5, 339404175309187222678927060006829975560488222720000000⟩,
  ⟨3, 2, 7, 1, 6, 5, 342380507537592855757244793574871517020458844160000000⟩,
  ⟨3, 2, 8, 1, 7, 5, -185787477806578405404929249675468866227221299200000000⟩,
  ⟨3, 2, 5, 2, 3, 5, -368667433552342779288553708295859907960284119040000000⟩,
  ⟨3, 2, 6, 2, 4, 5, -121816923025053157498335572375115102907866808320000000⟩,
  ⟨3, 2, 7, 2, 5, 5, -34724252473221966113059136977801396066084454400000000⟩,
  ⟨3, 2, 8, 2, 6, 5, -10109908137048192644336126202396873804742656000000000⟩,
  ⟨3, 2, 5, 3, 2, 5, 1001571417950149777375426179311426501732833689600000000⟩,
  ⟨3, 2, 6, 3, 3, 5, -184929354888250464846662264590902726850353561600000000⟩,
  ⟨3, 2, 7, 3, 4, 5, 139518433073147397274794567647778392019660963840000000⟩,
  ⟨3, 2, 8, 3, 5, 5, -160856407136013886183119199390411579379102515200000000⟩,
  ⟨3, 2, 5, 4, 1, 5, -277613767277352859675115691632168286263495884800000000⟩,
  ⟨3, 2, 6, 4, 2, 5, 562313720783050091480588509745797278527284838400000000⟩,
  ⟨3, 2, 7, 4, 3, 5, -494842435517035077968813239596966537149577953280000000⟩,
  ⟨3, 2, 8, 4, 4, 5, 230136339794848927577710515945128002889082470400000000⟩,
  ⟨3, 2, 5, 5, 0, 5, -3178129538116703209296507701322011255934560501760000000⟩,
  ⟨3, 2, 6, 5, 1, 5, -868939182440497576707745781611766888293780684800000000⟩,
  ⟨3, 2, 7, 5, 2, 5, 961183912341910354378085115904566364041715384320000000⟩,
  ⟨3, 2, 8, 5, 3, 5, -321922577370849555597481612194012292177723392000000000⟩,
  ⟨3, 2, 6, 6, 0, 5, 1274563998873961274351118506409556655261079306240000000⟩,
  ⟨3, 2, 7, 6, 1, 5, -2640821674319457560694823905388615927665304535040000000⟩,
  ⟨3, 2, 8, 6, 2, 5, 1148023093428502063664457851884692876145868144640000000⟩,
  ⟨3, 2, 7, 7, 0, 5, 8951493549782247673274175160628261412345269452800000000⟩,
  ⟨3, 2, 8, 7, 1, 5, -2146551144426836839523963551956443175643722547200000000⟩
]

def collectedFourData_10_0_27 : List CollectedFourTerm := [
  ⟨3, 3, 4, 0, 4, 6, -16391190905712743879552330490031987323530379264000000⟩,
  ⟨3, 3, 5, 0, 5, 6, 86213965181421718254549346733959920796324331520000000⟩,
  ⟨3, 3, 6, 0, 6, 6, 49827741464455613837244402275381654205675601920000000⟩,
  ⟨3, 3, 7, 0, 7, 6, -304450009431158472963871766885312532609761280000000⟩,
  ⟨3, 3, 8, 0, 8, 6, 10262998620346817924576323891949005763027927040000000⟩,
  ⟨3, 3, 4, 1, 3, 6, 9773105245774204887767620293756070881688289280000000⟩,
  ⟨3, 3, 5, 1, 4, 6, 46137241530035301830635252571762981014496870400000000⟩,
  ⟨3, 3, 6, 1, 5, 6, -31333659318456429649077177624954681388758466560000000⟩,
  ⟨3, 3, 7, 1, 6, 6, -21072288755611633398912580469648212739877765120000000⟩,
  ⟨3, 3, 8, 1, 7, 6, 8575913260235362399087790786623504384838860800000000⟩,
  ⟨3, 3, 4, 2, 2, 6, -6438447952084273093572865333325590199713923072000000⟩,
  ⟨3, 3, 5, 2, 3, 6, 68070463506911917834968359828915314505904291840000000⟩,
  ⟨3, 3, 6, 2, 4, 6, 11246090186758896175865577696720661610087055360000000⟩,
  ⟨3, 3, 7, 2, 5, 6, 2137152842610799065903741575300039689686220800000000⟩,
  ⟨3, 3, 8, 2, 6, 6, 466671361686374276099065227102955864326144000000000⟩,
  ⟨3, 3, 4, 3, 1, 6, 14294829711554518235959167751416406198104096768000000⟩,
  ⟨3, 3, 5, 3, 2, 6, -184929354888250464846662264590902726850353561600000000⟩,
  ⟨3, 3, 6, 3, 3, 6, 17072604951815144755275746267355034604588236800000000⟩,
  ⟨3, 3, 7, 3, 4, 6, -8586857732036727065585703324841884930413690880000000⟩,
  ⟨3, 3, 8, 3, 5, 6, 7425099964959610115405135806846132850314444800000000⟩,
  ⟨3, 3, 4, 4, 0, 6, -23877070640426475895343580757903094712008441856000000⟩,
  ⟨3, 3, 5, 4, 1, 6, 51258386541989962199788181429411942509628620800000000⟩,
  ⟨3, 3, 6, 4, 2, 6, -51912580453846856294588950870501396864774963200000000⟩,
  ⟨3, 3, 7, 4, 3, 6, 30455772043623638824627780890942841855892520960000000⟩,
  ⟨3, 3, 8, 4, 4, 6, -10623047965393033192948065079222487618263449600000000⟩,
  ⟨3, 3, 5, 5, 0, 6, 586807325670377523195653671430597294741740584960000000⟩,
  ⟨3, 3, 6, 5, 1, 6, 80220121883431669021079505672753615240324710400000000⟩,
  ⟨3, 3, 7, 5, 2, 6, -59157412592752054906320908768570038334773002240000000⟩,
  ⟨3, 3, 8, 5, 3, 6, 14859882553107455876878812632335740680798208000000000⟩,
  ⟨3, 3, 6, 6, 0, 6, -117667244617438717207375893293726416615526891520000000⟩,
  ⟨3, 3, 7, 6, 1, 6, 162533075476638546977855143359913813641296609280000000⟩,
  ⟨3, 3, 8, 6, 2, 6, -52992519120367244174906749431440611281846927360000000⟩,
  ⟨3, 3, 7, 7, 0, 6, -550932231018716528062433564458504753071626649600000000⟩,
  ⟨3, 3, 8, 7, 1, 6, 99084376625364173926638306701629412608888012800000000⟩
]

def collectedFourData_10_0_28 : List CollectedFourTerm := [
  ⟨3, 4, 3, 0, 3, 7, 2035363618983743401292342175024822576067117056000000⟩,
  ⟨3, 4, 4, 0, 4, 7, 24732398734098031738377918490031452835028349747200000⟩,
  ⟨3, 4, 5, 0, 5, 7, -65043418003612340136539698982750446891038670848000000⟩,
  ⟨3, 4, 6, 0, 6, 7, -25061420226823535332457896067275752486702415872000000⟩,
  ⟨3, 4, 7, 0, 7, 7, 114844904668076917089615440179112589379239936000000⟩,
  ⟨3, 4, 8, 0, 8, 7, -3097134009920533828665350678329942092900886118400000⟩,
  ⟨3, 4, 3, 1, 2, 7, -219235008188322729877632564258206911949281689600000⟩,
  ⟨3, 4, 4, 1, 3, 7, -14746477983155569646220698269441487084552454144000000⟩,
  ⟨3, 4, 5, 1, 4, 7, -34807862972742371746973007175042200251620392960000000⟩,
  ⟨3, 4, 6, 1, 5, 7, 15759614631221596605566196713080946471674576896000000⟩,
  ⟨3, 4, 7, 1, 6, 7, 7948907598321563344178634278163912137317023744000000⟩,
  ⟨3, 4, 8, 1, 7, 7, -2588010931984891752639561162425755882192109568000000⟩,
  ⟨3, 4, 3, 2, 1, 7, -1716248441672768077724073431465299451523052339200000⟩,
  ⟨3, 4, 4, 2, 2, 7, 9714868364091018302908841262764354356029004185600000⟩,
  ⟨3, 4, 5, 2, 3, 7, -51355202167801497237345199983237472758389538816000000⟩,
  ⟨3, 4, 6, 2, 4, 7, -5656346922329852134796878559394564398672510976000000⟩,
  ⟨3, 4, 7, 2, 5, 7, -806178705427977277410485988282556415433768960000000⟩,
  ⟨3, 4, 8, 2, 6, 7, -140830550524419107683849748547161152542474240000000⟩,
  ⟨3, 4, 3, 3, 0, 7, 17704079252369263528416883099672985716358381568000000⟩,
  ⟨3, 4, 4, 3, 1, 7, -21569233760737811359647334380916226009298527846400000⟩,
  ⟨3, 4, 5, 3, 2, 7, 139518433073147397274794567647778392019660963840000000⟩,
  ⟨3, 4, 6, 3, 3, 7, -8586857732036727065585703324841884930413690880000000⟩,
  ⟨3, 4, 7, 3, 4, 7, 3239142148415944054065317047496416919034003456000000⟩,
  ⟨3, 4, 8, 3, 5, 7, -2240722276133273985513642539102740280883806208000000⟩,
  ⟨3, 4, 4, 4, 0, 7, 36027719711045273539144109231408335570409934028800000⟩,
  ⟨3, 4, 5, 4, 1, 7, -38671468769886016477087604066741141513353297920000000⟩,
  ⟨3, 4, 6, 4, 2, 7, 26110013329436296135290673246408605932055429120000000⟩,
  ⟨3, 4, 7, 4, 3, 7, -11488553550968204116013379611177960636732669952000000⟩,
  ⟨3, 4, 8, 4, 4, 7, 3205788518514296384910016436761029501587030016000000⟩,
  ⟨3, 4, 5, 5, 0, 7, -442711967728693109483621599937043155057853333504000000⟩,
  ⟨3, 4, 6, 5, 1, 7, -40347608101037746455470315081831340504137072640000000⟩,
  ⟨3, 4, 7, 5, 2, 7, 22315412051780309474972496917436734462270373888000000⟩,
  ⟨3, 4, 8, 5, 3, 7, -4484366542485086693948474565672050942992711680000000⟩,
  ⟨3, 4, 6, 6, 0, 7, 59182057577176387606920632572336576322686943232000000⟩,
  ⟨3, 4, 7, 6, 1, 7, -61310871999643140797043574733463467512389697536000000⟩,
  ⟨3, 4, 8, 6, 2, 7, 15991908340869218840390844071711953446434871705600000⟩,
  ⟨3, 4, 7, 7, 0, 7, 207823148595507897974305639393683341724635627520000000⟩,
  ⟨3, 4, 8, 7, 1, 7, -29901357687975624889920390540002077645354303488000000⟩
]

def collectedFourData_10_0_29 : List CollectedFourTerm := [
  ⟨3, 5, 2, 0, 2, 8, -3839596996829086568264890875997395063505158144000000⟩,
  ⟨3, 5, 3, 0, 3, 8, -7039957482752723038955785868192486037431255040000000⟩,
  ⟨3, 5, 4, 0, 4, 8, -42772464318064457594634929416185992991026970624000000⟩,
  ⟨3, 5, 5, 0, 5, 8, 74991169965488310831034237188602994252778045440000000⟩,
  ⟨3, 5, 6, 0, 6, 8, 21670738732955357381799544745235358902512517120000000⟩,
  ⟨3, 5, 7, 0, 7, 8, -79445582934978145491871808830360215877582848000000⟩,
  ⟨3, 5, 8, 0, 8, 8, 1785405119169368770159543943941748718909259776000000⟩,
  ⟨3, 5, 2, 1, 1, 8, 20244351284257484867575977112358377099723014144000000⟩,
  ⟨3, 5, 3, 1, 2, 8, 758294548444055881996176532818050474588504064000000⟩,
  ⟨3, 5, 4, 1, 3, 8, 25502710437950868886330839422189336537837076480000000⟩,
  ⟨3, 5, 5, 1, 4, 8, 40131383750149511055425628075453863668010188800000000⟩,
  ⟨3, 5, 6, 1, 5, 8, -13627419679900193402979686620958242623360860160000000⟩,
  ⟨3, 5, 7, 1, 6, 8, -5498768967331219925181810008137354808647483392000000⟩,
  ⟨3, 5, 8, 1, 7, 8, 1491910892984146734151551414491091377345003520000000⟩,
  ⟨3, 5, 2, 2, 0, 8, -21399395829709151351066957494366666986193158144000000⟩,
  ⟨3, 5, 3, 2, 1, 8, 5936195354248103180214935432739442589096214528000000⟩,
  ⟨3, 5, 4, 2, 2, 8, -16800993099181096170031101847611886698183524352000000⟩,
  ⟨3, 5, 5, 2, 3, 8, 59209475955948856572952023048924919379766804480000000⟩,
  ⟨3, 5, 6, 2, 4, 8, 4891072222857127088920165520751041283316776960000000⟩,
  ⟨3, 5, 7, 2, 5, 8, 557685492339432669951182071684862475270881280000000⟩,
  ⟨3, 5, 8, 2, 6, 8, 81184600032269748585812494456489554581913600000000⟩,
  ⟨3, 5, 3, 3, 0, 8, -61235232881972677113178678794242059819674501120000000⟩,
  ⟨3, 5, 4, 3, 1, 8, 37302054334391053386160340668543207585861337088000000⟩,
  ⟨3, 5, 5, 3, 2, 8, -160856407136013886183119199390411579379102515200000000⟩,
  ⟨3, 5, 6, 3, 3, 8, 7425099964959610115405135806846132850314444800000000⟩,
  ⟨3, 5, 7, 3, 4, 8, -2240722276133273985513642539102740280883806208000000⟩,
  ⟨3, 5, 8, 3, 5, 8, 1291709370544103280276724484654004698213253120000000⟩,
  ⟨3, 5, 4, 4, 0, 8, -62306708393689908159472217163206128300034359296000000⟩,
  ⟨3, 5, 5, 4, 1, 8, 44585890107689851600404029549961214235875737600000000⟩,
  ⟨3, 5, 6, 4, 2, 8, -22577462572156563072085582704383240348840755200000000⟩,
  ⟨3, 5, 7, 4, 3, 8, 7947368989284264277195479497855489976236507136000000⟩,
  ⟨3, 5, 8, 4, 4, 8, -1848041193437628569770894366932482352469770240000000⟩,
  ⟨3, 5, 5, 5, 0, 8, 510420415111862492796168647246433818520972165120000000⟩,
  ⟨3, 5, 6, 5, 1, 8, 34888783865545717158514634961077089971103334400000000⟩,
  ⟨3, 5, 7, 5, 2, 8, -15437001093011661180121407463398667273302441984000000⟩,
  ⟨3, 5, 8, 5, 3, 8, 2585103181050323574175206649031771485844275200000000⟩,
  ⟨3, 5, 6, 6, 0, 8, -51175029021739767109502677027838099832145182720000000⟩,
  ⟨3, 5, 7, 6, 1, 8, 42412660625573416451667162859662653037528219648000000⟩,
  ⟨3, 5, 8, 6, 2, 8, -9218856828803419239721410648001378469579587584000000⟩,
  ⟨3, 5, 7, 7, 0, 8, -143764594827010367874992938479156367262597775360000000⟩,
  ⟨3, 5, 8, 7, 1, 8, 17237238335578452718715905841305842004336312320000000⟩
]

def collectedFourData_10_0_30 : List CollectedFourTerm := [
  ⟨4, 0, 6, 0, 6, 4, -69687110207117038620850698651215130723338315366400000⟩,
  ⟨4, 0, 7, 0, 7, 4, 1277375257410862306636392985195260139874864332800000⟩,
  ⟨4, 0, 8, 0, 8, 4, -86120545891703617804515911689718290701196512460800000⟩,
  ⟨4, 0, 6, 1, 5, 4, 43822017734341013452041821389735190044286858035200000⟩,
  ⟨4, 0, 7, 1, 6, 4, 88412611067834073181480565813921858337627124531200000⟩,
  ⟨4, 0, 8, 1, 7, 4, -71963600387428567312828278391106045905119215616000000⟩,
  ⟨4, 0, 6, 2, 4, 4, -15728337331984005991055420448013529654169383731200000⟩,
  ⟨4, 0, 7, 2, 5, 4, -8966812540282133320982783665976546634296721408000000⟩,
  ⟨4, 0, 8, 2, 6, 4, -3916008752137693578399073594983807124903034880000000⟩,
  ⟨4, 0, 6, 3, 3, 4, -23877070640426475895343580757903094712008441856000000⟩,
  ⟨4, 0, 7, 3, 4, 4, 36027719711045273539144109231408335570409934028800000⟩,
  ⟨4, 0, 8, 3, 5, 4, -62306708393689908159472217163206128300034359296000000⟩,
  ⟨4, 0, 6, 4, 2, 4, 72602883632678407888347905855190089300541702144000000⟩,
  ⟨4, 0, 7, 4, 3, 4, -127782717847696592148017721544427031882555300249600000⟩,
  ⟨4, 0, 8, 4, 4, 4, 89141850608811975949637834111795067379664289792000000⟩,
  ⟨4, 0, 6, 5, 1, 4, -112192692468449214472092168465008684517260525568000000⟩,
  ⟨4, 0, 7, 5, 2, 4, 248205658720841984506785023312384049920294151782400000⟩,
  ⟨4, 0, 8, 5, 3, 4, -124694667192400950625381383474514610540941148160000000⟩,
  ⟨4, 0, 6, 6, 0, 4, 164564758554681921093627932634032233280719709798400000⟩,
  ⟨4, 0, 7, 6, 1, 4, -681937009996039631746379597869927167106799684812800000⟩,
  ⟨4, 0, 8, 6, 2, 4, 444679459059339313991334919126472664450426155827200000⟩,
  ⟨4, 0, 7, 7, 0, 4, 2311536142594876029839688739922651628483322576896000000⟩,
  ⟨4, 0, 8, 7, 1, 4, -831452962236407062484205918833680277799652294656000000⟩
]

def collectedFourData_10_0_31 : List CollectedFourTerm := [
  ⟨4, 1, 5, 0, 5, 5, 129423388084579729722618086854805497664042434560000000⟩,
  ⟨4, 1, 6, 0, 6, 5, 149601636054248313271782891010373344095130091520000000⟩,
  ⟨4, 1, 7, 0, 7, 5, -1371110294256147017973582779904670876324331520000000⟩,
  ⟨4, 1, 8, 0, 8, 5, 61626770120480779596966521755244213544922644480000000⟩,
  ⟨4, 1, 5, 1, 4, 5, 69260683035844086482212036132062183682159411200000000⟩,
  ⟨4, 1, 6, 1, 5, 5, -94075439902315837477779644591295356130935439360000000⟩,
  ⟨4, 1, 7, 1, 6, 5, -94900414325295838706636832652306611353765806080000000⟩,
  ⟨4, 1, 8, 1, 7, 5, 51496239511707906755366490008428457921976729600000000⟩,
  ⟨4, 1, 5, 2, 3, 5, 102186577279138232382127739749180536281125355520000000⟩,
  ⟨4, 1, 6, 2, 4, 5, 33764995998321816082029368865433671591694172160000000⟩,
  ⟨4, 1, 7, 2, 5, 5, 9624805952141184287223816441894261014868787200000000⟩,
  ⟨4, 1, 8, 2, 6, 5, 2802246184798382045642543346390472461385728000000000⟩,
  ⟨4, 1, 5, 3, 2, 5, -277613767277352859675115691632168286263495884800000000⟩,
  ⟨4, 1, 6, 3, 3, 5, 51258386541989962199788181429411942509628620800000000⟩,
  ⟨4, 1, 7, 3, 4, 5, -38671468769886016477087604066741141513353297920000000⟩,
  ⟨4, 1, 8, 3, 5, 5, 44585890107689851600404029549961214235875737600000000⟩,
  ⟨4, 1, 5, 4, 1, 5, 76948485550493347382545845165693215317583462400000000⟩,
  ⟨4, 1, 6, 4, 2, 5, -155861107476309547648813716232416058607350579200000000⟩,
  ⟨4, 1, 7, 4, 3, 5, 137159537772894093048462051676284106268360048640000000⟩,
  ⟨4, 1, 8, 4, 4, 5, -63788777447969141921694230032206048636646195200000000⟩,
  ⟨4, 1, 5, 5, 0, 5, 880908238952885985003255946802193681380938874880000000⟩,
  ⟨4, 1, 6, 5, 1, 5, 240851002383752157797717473371791520728245862400000000⟩,
  ⟨4, 1, 7, 5, 2, 5, -266419230989780191783845427829103112736640860160000000⟩,
  ⟨4, 1, 8, 5, 3, 5, 89229921974475493691337118441412419173482496000000000⟩,
  ⟨4, 1, 6, 6, 0, 5, -353281360691843616478859375807098034611940229120000000⟩,
  ⟨4, 1, 7, 6, 1, 5, 731978210017171730844402798828458280253673963520000000⟩,
  ⟨4, 1, 8, 6, 2, 5, -318206979728278927161617031831523996167642808320000000⟩,
  ⟨4, 1, 7, 7, 0, 5, -2481158909466464492004838765370189588008953446400000000⟩,
  ⟨4, 1, 8, 7, 1, 5, 594977192018379936176411065108478092046342553600000000⟩
]

def collectedFourData_10_0_32 : List CollectedFourTerm := [
  ⟨4, 2, 4, 0, 4, 6, 49840608332983644557041530116427295432938356736000000⟩,
  ⟨4, 2, 5, 0, 5, 6, -262150352354393679784430597346366438959984148480000000⟩,
  ⟨4, 2, 6, 0, 6, 6, -151510952482504359647373237511006790292162478080000000⟩,
  ⟨4, 2, 7, 0, 7, 6, 925739549024655262842043497305383826588958720000000⟩,
  ⟨4, 2, 8, 0, 8, 6, -31206646149205771505164031890625830218325032960000000⟩,
  ⟨4, 2, 4, 1, 3, 6, -29717029931113438794914168936067090094982430720000000⟩,
  ⟨4, 2, 5, 1, 4, 6, -140289268662066517586951587850460317781432729600000000⟩,
  ⟨4, 2, 6, 1, 5, 6, 95276093769735927536348091424588632398694973440000000⟩,
  ⟨4, 2, 7, 1, 6, 6, 64074398046449090175686064253057394298197114880000000⟩,
  ⟨4, 2, 8, 1, 7, 6, -26076734531354999487950327615014213201900339200000000⟩,
  ⟨4, 2, 4, 2, 2, 6, 19577354964506727076569208384123361083867004928000000⟩,
  ⟨4, 2, 5, 2, 3, 6, -206981501845007546383580657847361895552683868160000000⟩,
  ⟨4, 2, 6, 2, 4, 6, -34195927525943734603122843577692825370377584640000000⟩,
  ⟨4, 2, 7, 2, 5, 6, -6498429454516548411712280422319984569692979200000000⟩,
  ⟨4, 2, 8, 2, 6, 6, -1419005165141741896792067141538534817529856000000000⟩,
  ⟨4, 2, 4, 3, 1, 6, -43466213830257749159451298280538220759175135232000000⟩,
  ⟨4, 2, 5, 3, 2, 6, 562313720783050091480588509745797278527284838400000000⟩,
  ⟨4, 2, 6, 3, 3, 6, -51912580453846856294588950870501396864774963200000000⟩,
  ⟨4, 2, 7, 3, 4, 6, 26110013329436296135290673246408605932055429120000000⟩,
  ⟨4, 2, 8, 3, 5, 6, -22577462572156563072085582704383240348840755200000000⟩,
  ⟨4, 2, 4, 4, 0, 6, 72602883632678407888347905855190089300541702144000000⟩,
  ⟨4, 2, 5, 4, 1, 6, -155861107476309547648813716232416058607350579200000000⟩,
  ⟨4, 2, 6, 4, 2, 6, 157850311477546460258401430125377844702661836800000000⟩,
  ⟨4, 2, 7, 4, 3, 6, -92606706531362541762207763935955370378306519040000000⟩,
  ⟨4, 2, 8, 4, 4, 6, 32301446306816124716819557497415063065486950400000000⟩,
  ⟨4, 2, 5, 5, 0, 6, -1784301961578008660116367537088477000092394455040000000⟩,
  ⟨4, 2, 6, 5, 1, 6, -243924904432834563420981474505570172607764889600000000⟩,
  ⟨4, 2, 7, 5, 2, 6, 179879634615228804136212099023314179027904757760000000⟩,
  ⟨4, 2, 8, 5, 3, 6, -45184367045925810318460165802976269976993792000000000⟩,
  ⟨4, 2, 6, 6, 0, 6, 357790174389048046359484067820599821858221588480000000⟩,
  ⟨4, 2, 7, 6, 1, 6, -494213471283718367749612545606808005967054110720000000⟩,
  ⟨4, 2, 8, 6, 2, 6, 161134075324316617002129497355597459042745712640000000⟩,
  ⟨4, 2, 7, 7, 0, 6, 1675216749177793365584312416655922486648923750400000000⟩,
  ⟨4, 2, 8, 7, 1, 6, -301285345019162060185673790790765000992699187200000000⟩
]

def collectedFourData_10_0_33 : List CollectedFourTerm := [
  ⟨4, 3, 3, 0, 3, 7, -7219005175127151536120010153823066278070321152000000⟩,
  ⟨4, 3, 4, 0, 4, 7, -87720598319384592052547382053053402388168599142400000⟩,
  ⟨4, 3, 5, 0, 5, 7, 230695275672895056877580102897918866197646934016000000⟩,
  ⟨4, 3, 6, 0, 6, 7, 88887568111199683863899298019928251525679284224000000⟩,
  ⟨4, 3, 7, 0, 7, 7, -407330637829610060713486783969113277162586112000000⟩,
  ⟨4, 3, 8, 0, 8, 7, 10984880655792647923663897784541392236637375692800000⟩,
  ⟨4, 3, 3, 1, 2, 7, 777580302565674404225938048761894328811598643200000⟩,
  ⟨4, 3, 4, 1, 3, 7, 52302645032267780033311546702126592428760629248000000⟩,
  ⟨4, 3, 5, 1, 4, 7, 123456143458438674102786848654794407887052472320000000⟩,
  ⟨4, 3, 6, 1, 5, 7, -55896026891550212461025817045065576954757906432000000⟩,
  ⟨4, 3, 7, 1, 6, 7, -28193097564327264700287240413521490257744232448000000⟩,
  ⟨4, 3, 8, 1, 7, 7, 9179128553262107589530151597619980000093536256000000⟩,
  ⟨4, 3, 3, 2, 1, 7, 6087170993272322379802582817302518816284501606400000⟩,
  ⟨4, 3, 4, 2, 2, 7, -34456587678946939384273416673841202866878100275200000⟩,
  ⟨4, 3, 5, 2, 3, 7, 182146063121717414969124644509163802487079043072000000⟩,
  ⟨4, 3, 6, 2, 4, 7, 20061868711695724068583319813132458692855201792000000⟩,
  ⟨4, 3, 7, 2, 5, 7, 2859345717040822597153590078414552322875064320000000⟩,
  ⟨4, 3, 8, 2, 6, 7, 499496239182757758129496444229320991393710080000000⟩,
  ⟨4, 3, 3, 3, 0, 7, -62792632506386437441556306954498768597214560256000000⟩,
  ⟨4, 3, 4, 3, 1, 7, 76501519772687451055667031504020937622902590668800000⟩,
  ⟨4, 3, 5, 3, 2, 7, -494842435517035077968813239596966537149577953280000000⟩,
  ⟨4, 3, 6, 3, 3, 7, 30455772043623638824627780890942841855892520960000000⟩,
  ⟨4, 3, 7, 3, 4, 7, -11488553550968204116013379611177960636732669952000000⟩,
  ⟨4, 3, 8, 3, 5, 7, 7947368989284264277195479497855489976236507136000000⟩,
  ⟨4, 3, 4, 4, 0, 7, -127782717847696592148017721544427031882555300249600000⟩,
  ⟨4, 3, 5, 4, 1, 7, 137159537772894093048462051676284106268360048640000000⟩,
  ⟨4, 3, 6, 4, 2, 7, -92606706531362541762207763935955370378306519040000000⟩,
  ⟨4, 3, 7, 4, 3, 7, 40747474684928665982047713702411512564190019584000000⟩,
  ⟨4, 3, 8, 4, 4, 7, -11370255265284247731169427198249558407718633472000000⟩,
  ⟨4, 3, 5, 5, 0, 7, 1570205911275888963156575853624177875007326650368000000⟩,
  ⟨4, 3, 6, 5, 1, 7, 143104450216529131398237563749015219986109562880000000⟩,
  ⟨4, 3, 7, 5, 2, 7, -79148056683518592055790183978498486908219293696000000⟩,
  ⟨4, 3, 8, 5, 3, 7, 15905101661161928802978102144575739718596034560000000⟩,
  ⟨4, 3, 6, 6, 0, 7, -209906267332039678905200128067821865057956921344000000⟩,
  ⟨4, 3, 7, 6, 1, 7, 217456722783506385254544038547053523537663885312000000⟩,
  ⟨4, 3, 8, 6, 2, 7, -56719923652038129288956844649082140894717752115200000⟩,
  ⟨4, 3, 7, 7, 0, 7, -737104845163380778443791042781854777258897571840000000⟩,
  ⟨4, 3, 8, 7, 1, 7, 106053804774501154656795224635543932091704016896000000⟩
]

def collectedFourData_10_0_34 : List CollectedFourTerm := [
  ⟨4, 4, 2, 0, 2, 8, 5493289417998603593850991673925282282589913088000000⟩,
  ⟨4, 4, 3, 0, 3, 8, 10072026823414838973940589130256982330132398080000000⟩,
  ⟨4, 4, 4, 0, 4, 8, 61194319563794906930353274385656381369166594048000000⟩,
  ⟨4, 4, 5, 0, 5, 8, -107289437082838944318694627854289601521652858880000000⟩,
  ⟨4, 4, 6, 0, 6, 8, -31004201706655091940868950012425546697529098240000000⟩,
  ⟨4, 4, 7, 0, 7, 8, 113662340189311360431830360531002435143991296000000⟩,
  ⟨4, 4, 8, 0, 8, 8, -2554368871543891671067249385432376985100746752000000⟩,
  ⟨4, 4, 2, 1, 1, 8, -28963477358665183262743817889400144522628825088000000⟩,
  ⟨4, 4, 3, 1, 2, 8, -1084887664547567497796685858027680323420028928000000⟩,
  ⟨4, 4, 4, 1, 3, 8, -36486581663329207046954467751530108998868008960000000⟩,
  ⟨4, 4, 5, 1, 4, 8, -57415740731748089387226657437983526687971737600000000⟩,
  ⟨4, 4, 6, 1, 5, 8, 19496671235039486435012799193211806551449272320000000⟩,
  ⟨4, 4, 7, 1, 6, 8, 7867057247207312927537117184387642626024669184000000⟩,
  ⟨4, 4, 8, 1, 7, 8, -2134468364204596156471437440490281089672151040000000⟩,
  ⟨4, 4, 2, 2, 0, 8, 30615992970091754999659202418367927401565913088000000⟩,
  ⟨4, 4, 3, 2, 1, 8, -8492880672006402391641900491423302838340550656000000⟩,
  ⟨4, 4, 4, 2, 2, 8, 24037084537731067418492822469613293242998063104000000⟩,
  ⟨4, 4, 5, 2, 3, 8, -84710657910886681718378570284268784748289064960000000⟩,
  ⟨4, 4, 6, 2, 4, 8, -6997628997698675100334974393680606844074065920000000⟩,
  ⟨4, 4, 7, 2, 5, 8, -797877437702328415873932985578854313162178560000000⟩,
  ⟨4, 4, 8, 2, 6, 8, -116150341983812150402860171561589546365747200000000⟩,
  ⟨4, 4, 3, 3, 0, 8, 87608896735001321308390624836450169764697866240000000⟩,
  ⟨4, 4, 4, 3, 1, 8, -53367835351976810108518040556369915987703627776000000⟩,
  ⟨4, 4, 5, 3, 2, 8, 230136339794848927577710515945128002889082470400000000⟩,
  ⟨4, 4, 6, 3, 3, 8, -10623047965393033192948065079222487618263449600000000⟩,
  ⟨4, 4, 7, 3, 4, 8, 3205788518514296384910016436761029501587030016000000⟩,
  ⟨4, 4, 8, 3, 5, 8, -1848041193437628569770894366932482352469770240000000⟩,
  ⟨4, 4, 4, 4, 0, 8, 89141850608811975949637834111795067379664289792000000⟩,
  ⟨4, 4, 5, 4, 1, 8, -63788777447969141921694230032206048636646195200000000⟩,
  ⟨4, 4, 6, 4, 2, 8, 32301446306816124716819557497415063065486950400000000⟩,
  ⟨4, 4, 7, 4, 3, 8, -11370255265284247731169427198249558407718633472000000⟩,
  ⟨4, 4, 8, 4, 4, 8, 2643981944021800545425633074876344070286868480000000⟩,
  ⟨4, 4, 5, 5, 0, 8, -730255562596810533964777595301194060148233994240000000⟩,
  ⟨4, 4, 6, 5, 1, 8, -49915183123051567277026742452100005247110348800000000⟩,
  ⟨4, 4, 7, 5, 2, 8, 22085628991768004143775841578289742577053728768000000⟩,
  ⟨4, 4, 8, 5, 3, 8, -3698492305475254223324790336303042721637990400000000⟩,
  ⟨4, 4, 6, 6, 0, 8, 73215820728856576055209703031950706791090749440000000⟩,
  ⟨4, 4, 7, 6, 1, 8, -60679550483042383128824379684795106817942224896000000⟩,
  ⟨4, 4, 8, 6, 2, 8, 13189365630177418066586581551048296407360339968000000⟩,
  ⟨4, 4, 7, 7, 0, 8, 205683181880357861714706488821683845824480542720000000⟩,
  ⟨4, 4, 8, 7, 1, 8, -24661218097251238802003073771001118500470128640000000⟩
]

def collectedFourData_10_0_35 : List CollectedFourTerm := [
  ⟨5, 0, 5, 0, 5, 5, 1481642270946190090178591663754775448798701289472000000⟩,
  ⟨5, 0, 6, 0, 6, 5, 1712643371967877907943757460661996417476223565824000000⟩,
  ⟨5, 0, 7, 0, 7, 5, -15696505864703297509914007827016512451928653824000000⟩,
  ⟨5, 0, 8, 0, 8, 5, 705504847181998864521161885580236561179660517376000000⟩,
  ⟨5, 0, 5, 1, 4, 5, 792898078309070308282554684256365634288814653440000000⟩,
  ⟨5, 0, 6, 1, 5, 5, -1076978052267018014428391960824762086636474335232000000⟩,
  ⟨5, 0, 7, 1, 6, 5, -1086422380650214203566469912169971014726420791296000000⟩,
  ⟨5, 0, 8, 1, 7, 5, 589530272576804394361576404587312682758590955520000000⟩,
  ⟨5, 0, 5, 2, 3, 5, 1169834561286067013077108055358966182425997082624000000⟩,
  ⟨5, 0, 6, 2, 4, 5, 386542541420325765998393937601673078482604654592000000⟩,
  ⟨5, 0, 7, 2, 5, 5, 110185025746872365622729336722080137652878704640000000⟩,
  ⟨5, 0, 8, 2, 6, 5, 32080186297407377020945432838794452825381273600000000⟩,
  ⟨5, 0, 5, 3, 2, 5, -3178129538116703209296507701322011255934560501760000000⟩,
  ⟨5, 0, 6, 3, 3, 5, 586807325670377523195653671430597294741740584960000000⟩,
  ⟨5, 0, 7, 3, 4, 5, -442711967728693109483621599937043155057853333504000000⟩,
  ⟨5, 0, 8, 3, 5, 5, 510420415111862492796168647246433818520972165120000000⟩,
  ⟨5, 0, 5, 4, 1, 5, 880908238952885985003255946802193681380938874880000000⟩,
  ⟨5, 0, 6, 4, 2, 5, -1784301961578008660116367537088477000092394455040000000⟩,
  ⟨5, 0, 7, 4, 3, 5, 1570205911275888963156575853624177875007326650368000000⟩,
  ⟨5, 0, 8, 4, 4, 5, -730255562596810533964777595301194060148233994240000000⟩,
  ⟨5, 0, 5, 5, 0, 5, 10084660145076755605488052657091431422648549113856000000⟩,
  ⟨5, 0, 6, 5, 1, 5, 2757268461387518063002953266514285395872453754880000000⟩,
  ⟨5, 0, 7, 5, 2, 5, -3049974199172328211066682834228076340716547080192000000⟩,
  ⟨5, 0, 8, 5, 3, 5, 1021506438575186132256541261766698052044927795200000000⟩,
  ⟨5, 0, 6, 6, 0, 5, -4044374090997766195260067057901235960614637010944000000⟩,
  ⟨5, 0, 7, 6, 1, 5, 8379705348651639201941684612732038100173637812224000000⟩,
  ⟨5, 0, 8, 6, 2, 5, -3642841676864655244737983910206976432750653865984000000⟩,
  ⟨5, 0, 7, 7, 0, 5, -28404370922493783701122241852518085603989578055680000000⟩,
  ⟨5, 0, 8, 7, 1, 5, 6811314175821148657321187160084762220665577144320000000⟩
]

def collectedFourData_10_0_36 : List CollectedFourTerm := [
  ⟨5, 1, 4, 0, 4, 6, -77018318878811381784103020861878239306859937792000000⟩,
  ⟨5, 1, 5, 0, 5, 6, 405098976660399505155994686407473453746156994560000000⟩,
  ⟨5, 1, 6, 0, 6, 6, 234128740443313180006129943565075226205890805760000000⟩,
  ⟨5, 1, 7, 0, 7, 6, -1430538393696201561440715987094895702405283840000000⟩,
  ⟨5, 1, 8, 0, 8, 6, 48223396636737638020596900553599736272251781120000000⟩,
  ⟨5, 1, 4, 1, 3, 6, 45921503848319172681602500462469587287240867840000000⟩,
  ⟨5, 1, 5, 1, 4, 6, 216787956457181176318534376548490070795170611200000000⟩,
  ⟨5, 1, 6, 1, 5, 6, -147229434329133032061055345372195290500227399680000000⟩,
  ⟨5, 1, 7, 1, 6, 6, -99013687548501947271868757264271006061937295360000000⟩,
  ⟨5, 1, 8, 1, 7, 6, 40296182623535444745159548236187746961876582400000000⟩,
  ⟨5, 1, 4, 2, 2, 6, -30252740042545077900234201345294561173324169216000000⟩,
  ⟨5, 1, 5, 2, 3, 6, 319846965041242463173578204583082574785040875520000000⟩,
  ⟨5, 1, 6, 2, 4, 6, 52842710766170824060601315015974696549173166080000000⟩,
  ⟨5, 1, 7, 2, 5, 6, 10041974379518054891013698029273878188418662400000000⟩,
  ⟨5, 1, 8, 2, 6, 6, 2192778056989349995429955949078431957778432000000000⟩,
  ⟨5, 1, 4, 3, 1, 6, 67168014781592199360472209671686831665057890304000000⟩,
  ⟨5, 1, 5, 3, 2, 6, -868939182440497576707745781611766888293780684800000000⟩,
  ⟨5, 1, 6, 3, 3, 6, 80220121883431669021079505672753615240324710400000000⟩,
  ⟨5, 1, 7, 3, 4, 6, -40347608101037746455470315081831340504137072640000000⟩,
  ⟨5, 1, 8, 3, 5, 6, 34888783865545717158514634961077089971103334400000000⟩,
  ⟨5, 1, 4, 4, 0, 6, -112192692468449214472092168465008684517260525568000000⟩,
  ⟨5, 1, 5, 4, 1, 6, 240851002383752157797717473371791520728245862400000000⟩,
  ⟨5, 1, 6, 4, 2, 6, -243924904432834563420981474505570172607764889600000000⟩,
  ⟨5, 1, 7, 4, 3, 6, 143104450216529131398237563749015219986109562880000000⟩,
  ⟨5, 1, 8, 4, 4, 6, -49915183123051567277026742452100005247110348800000000⟩,
  ⟨5, 1, 5, 5, 0, 6, 2757268461387518063002953266514285395872453754880000000⟩,
  ⟨5, 1, 6, 5, 1, 6, 376935328449009790046424749349492332000654131200000000⟩,
  ⟨5, 1, 7, 5, 2, 6, -277966652534443819475705125303720677351327006720000000⟩,
  ⟨5, 1, 8, 5, 3, 6, 69823064081209289226248389660061984435994624000000000⟩,
  ⟨5, 1, 6, 6, 0, 6, -552890477553920478631006721603531006355764674560000000⟩,
  ⟨5, 1, 7, 6, 1, 6, 763704376785143678802274220721392767310065827840000000⟩,
  ⟨5, 1, 8, 6, 2, 6, -248999280118291132069503814933692866306852782080000000⟩,
  ⟨5, 1, 7, 7, 0, 6, -2588699899433537145530938502333594095047199948800000000⟩,
  ⟨5, 1, 8, 7, 1, 6, 465573987804683416830434790386327234552424038400000000⟩
]

def collectedFourData_10_0_37 : List CollectedFourTerm := [
  ⟨5, 2, 3, 0, 3, 7, 14022224327214846439497205903568886381504626688000000⟩,
  ⟨5, 2, 4, 0, 4, 7, 170388838615876348641067700040765087133147437465600000⟩,
  ⟨5, 2, 5, 0, 5, 7, -448103419825714057821343909680259247665739464704000000⟩,
  ⟨5, 2, 6, 0, 6, 7, -172655565374889401627039102556408332306513657856000000⟩,
  ⟨5, 2, 7, 0, 7, 7, 791200648902941925597007357036935939178364928000000⟩,
  ⟨5, 2, 8, 0, 8, 7, -21337075819521683846608881602476407533279064883200000⟩,
  ⟨5, 2, 3, 1, 2, 7, -1510375068377400629230886162383073878517533900800000⟩,
  ⟨5, 2, 4, 1, 3, 7, -101592865465182370273079008942712732275716390912000000⟩,
  ⟨5, 2, 5, 1, 4, 7, -239801703441299118800128600349045635737012142080000000⟩,
  ⟨5, 2, 6, 1, 5, 7, 108572664662142379082069329767418447921579819008000000⟩,
  ⟨5, 2, 7, 1, 6, 7, 54762384696460379495998809003114962932268531712000000⟩,
  ⟨5, 2, 8, 1, 7, 7, -17829575762829022406116326513573477896121483264000000⟩,
  ⟨5, 2, 3, 2, 1, 7, -11823745116552892881131418525043359631971817881600000⟩,
  ⟨5, 2, 4, 2, 2, 7, 66928612774686234856690687815786946225765141708800000⟩,
  ⟨5, 2, 5, 2, 3, 7, -353801236521037756511227167021098161233532551168000000⟩,
  ⟨5, 2, 6, 2, 4, 7, -38968253474562065157341042830334498515974094848000000⟩,
  ⟨5, 2, 7, 2, 5, 7, -5554004478560468841806837749287905136822190080000000⟩,
  ⟨5, 2, 8, 2, 6, 7, -970223479067865610413402658410883605615083520000000⟩,
  ⟨5, 2, 3, 3, 0, 7, 121968658802825301638772061248054184640998539264000000⟩,
  ⟨5, 2, 4, 3, 1, 7, -148596855882790144559161164692107273986204971827200000⟩,
  ⟨5, 2, 5, 3, 2, 7, 961183912341910354378085115904566364041715384320000000⟩,
  ⟨5, 2, 6, 3, 3, 7, -59157412592752054906320908768570038334773002240000000⟩,
  ⟨5, 2, 7, 3, 4, 7, 22315412051780309474972496917436734462270373888000000⟩,
  ⟨5, 2, 8, 3, 5, 7, -15437001093011661180121407463398667273302441984000000⟩,
  ⟨5, 2, 4, 4, 0, 7, 248205658720841984506785023312384049920294151782400000⟩,
  ⟨5, 2, 5, 4, 1, 7, -266419230989780191783845427829103112736640860160000000⟩,
  ⟨5, 2, 6, 4, 2, 7, 179879634615228804136212099023314179027904757760000000⟩,
  ⟨5, 2, 7, 4, 3, 7, -79148056683518592055790183978498486908219293696000000⟩,
  ⟨5, 2, 8, 4, 4, 7, 22085628991768004143775841578289742577053728768000000⟩,
  ⟨5, 2, 5, 5, 0, 7, -3049974199172328211066682834228076340716547080192000000⟩,
  ⟨5, 2, 6, 5, 1, 7, -277966652534443819475705125303720677351327006720000000⟩,
  ⟨5, 2, 7, 5, 2, 7, 153737499690858174292432870643831556779355930624000000⟩,
  ⟨5, 2, 8, 5, 3, 7, -30894132644258954584596262201791787997740400640000000⟩,
  ⟨5, 2, 6, 6, 0, 7, 407722767447156901372659797635922619069823451136000000⟩,
  ⟨5, 2, 7, 6, 1, 7, -422388802107707424836827714856296500441517129728000000⟩,
  ⟨5, 2, 8, 6, 2, 7, 110173005002364352296972475469593335968782142668800000⟩,
  ⟨5, 2, 7, 7, 0, 7, 1431755379144168669580147098474173717281725480960000000⟩,
  ⟨5, 2, 8, 7, 1, 7, -205999331656734958776253737402024749999717351424000000⟩
]

def collectedFourData_10_0_38 : List CollectedFourTerm := [
  ⟨5, 3, 2, 0, 2, 8, -7684200979569531098105583043255061547570954240000000⟩,
  ⟨5, 3, 3, 0, 3, 8, -14089095347707487631038098421247915661354598400000000⟩,
  ⟨5, 3, 4, 0, 4, 8, -85600705616476455266225860449676902360196055040000000⟩,
  ⟨5, 3, 5, 0, 5, 8, 150080131374142021178366703501375330742330982400000000⟩,
  ⟨5, 3, 6, 0, 6, 8, 43369736963877359486799152336557012025553715200000000⟩,
  ⟨5, 3, 7, 0, 7, 8, -158994766043308745225905477394598524438446080000000⟩,
  ⟨5, 3, 8, 0, 8, 8, 3573138477027623393499962673696811670002728960000000⟩,
  ⟨5, 3, 2, 1, 1, 8, 40515102000994099445315102287051857441576714240000000⟩,
  ⟨5, 3, 3, 1, 2, 8, 1517577942885192832692634880249775489747517440000000⟩,
  ⟨5, 3, 4, 1, 3, 8, 51038677416098460303865465530263627031694540800000000⟩,
  ⟨5, 3, 5, 1, 4, 8, 80315100407426056942239864247011620262248448000000000⟩,
  ⟨5, 3, 6, 1, 5, 8, -27272610052506358765795319737706128000784793600000000⟩,
  ⟨5, 3, 7, 1, 6, 8, -11004708546258390460300990067257403150507704320000000⟩,
  ⟨5, 3, 8, 1, 7, 8, 2985767296611296404300798112054294210622259200000000⟩,
  ⟨5, 3, 2, 2, 0, 8, -42826697315537789319428807733332507200050954240000000⟩,
  ⟨5, 3, 3, 2, 1, 8, 11880131741352085501267644045828820967494778880000000⟩,
  ⟨5, 3, 4, 2, 2, 8, -33623895355967507201557924622620025685981265920000000⟩,
  ⟨5, 3, 5, 2, 3, 8, 118496163403670197303787950457229370521865420800000000⟩,
  ⟨5, 3, 6, 2, 4, 8, 9788522596788834262243051765570607672564121600000000⟩,
  ⟨5, 3, 7, 2, 5, 8, 1116098228555089405907490207387570550918348800000000⟩,
  ⟨5, 3, 8, 2, 6, 8, 162475067984770840136558665724246366355456000000000⟩,
  ⟨5, 3, 3, 3, 0, 8, -122550318922641948799727202068225671577154355200000000⟩,
  ⟨5, 3, 4, 3, 1, 8, 74652752018766818459784295820902179023597076480000000⟩,
  ⟨5, 3, 5, 3, 2, 8, -321922577370849555597481612194012292177723392000000000⟩,
  ⟨5, 3, 6, 3, 3, 8, 14859882553107455876878812632335740680798208000000000⟩,
  ⟨5, 3, 7, 3, 4, 8, -4484366542485086693948474565672050942992711680000000⟩,
  ⟨5, 3, 8, 3, 5, 8, 2585103181050323574175206649031771485844275200000000⟩,
  ⟨5, 3, 4, 4, 0, 8, -124694667192400950625381383474514610540941148160000000⟩,
  ⟨5, 3, 5, 4, 1, 8, 89229921974475493691337118441412419173482496000000000⟩,
  ⟨5, 3, 6, 4, 2, 8, -45184367045925810318460165802976269976993792000000000⟩,
  ⟨5, 3, 7, 4, 3, 8, 15905101661161928802978102144575739718596034560000000⟩,
  ⟨5, 3, 8, 4, 4, 8, -3698492305475254223324790336303042721637990400000000⟩,
  ⟨5, 3, 5, 5, 0, 8, 1021506438575186132256541261766698052044927795200000000⟩,
  ⟨5, 3, 6, 5, 1, 8, 69823064081209289226248389660061984435994624000000000⟩,
  ⟨5, 3, 7, 5, 2, 8, -30894132644258954584596262201791787997740400640000000⟩,
  ⟨5, 3, 8, 5, 3, 8, 5173577438601023362750162451839368919252992000000000⟩,
  ⟨5, 3, 6, 6, 0, 8, -102416792299584222906306445274117079880119091200000000⟩,
  ⟨5, 3, 7, 6, 1, 8, 84880629033289289216998515651816859094828974080000000⟩,
  ⟨5, 3, 8, 6, 2, 8, -18449735410488394745197941798726738524126576640000000⟩,
  ⟨5, 3, 7, 7, 0, 8, -287716664355518156610612247234098705901132185600000000⟩,
  ⟨5, 3, 8, 7, 1, 8, 34496954709755288701692495810464937848025907200000000⟩
]

def collectedFourData_10_0_39 : List CollectedFourTerm := [
  ⟨6, 0, 4, 0, 4, 6, 112970825208989558059914145191193782674469263769600000⟩,
  ⟨6, 0, 5, 0, 5, 6, -594201046593251883476200718611438784867758768128000000⟩,
  ⟨6, 0, 6, 0, 6, 6, -343421115885964067502171608100494668020672626688000000⟩,
  ⟨6, 0, 7, 0, 7, 6, 2098320311084624107717167942470376730543521792000000⟩,
  ⟨6, 0, 8, 0, 8, 6, -70734300511088209629773191628555749100781305856000000⟩,
  ⟨6, 0, 4, 1, 3, 6, -67357873556619876605627245761314433536719060992000000⟩,
  ⟨6, 0, 5, 1, 4, 6, -317985573988890697551786766421273375981237698560000000⟩,
  ⟨6, 0, 6, 1, 5, 6, 215956813045820986405550826350598398738310365184000000⟩,
  ⟨6, 0, 7, 1, 6, 6, 145233733378938000017669167894231177525532295168000000⟩,
  ⟨6, 0, 8, 1, 7, 6, -59106626449689136871941704888519490180082565120000000⟩,
  ⟨6, 0, 4, 2, 2, 6, 44374858568609983751104585006888452061754346700800000⟩,
  ⟨6, 0, 5, 2, 3, 6, -469153002912930365506705502546261794501297176576000000⟩,
  ⟨6, 0, 6, 2, 4, 6, -77509931772564347766294561898555488393184149504000000⟩,
  ⟨6, 0, 7, 2, 5, 6, -14729614316390716823020330564873774867540869120000000⟩,
  ⟨6, 0, 8, 2, 6, 6, -3216376963356469544625650659061511415765401600000000⟩,
  ⟨6, 0, 4, 3, 1, 6, -98522353746332313669161834086819879556727649075200000⟩,
  ⟨6, 0, 5, 3, 2, 6, 1274563998873961274351118506409556655261079306240000000⟩,
  ⟨6, 0, 6, 3, 3, 6, -117667244617438717207375893293726416615526891520000000⟩,
  ⟨6, 0, 7, 3, 4, 6, 59182057577176387606920632572336576322686943232000000⟩,
  ⟨6, 0, 8, 3, 5, 6, -51175029021739767109502677027838099832145182720000000⟩,
  ⟨6, 0, 4, 4, 0, 6, 164564758554681921093627932634032233280719709798400000⟩,
  ⟨6, 0, 5, 4, 1, 6, -353281360691843616478859375807098034611940229120000000⟩,
  ⟨6, 0, 6, 4, 2, 6, 357790174389048046359484067820599821858221588480000000⟩,
  ⟨6, 0, 7, 4, 3, 6, -209906267332039678905200128067821865057956921344000000⟩,
  ⟨6, 0, 8, 4, 4, 6, 73215820728856576055209703031950706791090749440000000⟩,
  ⟨6, 0, 5, 5, 0, 6, -4044374090997766195260067057901235960614637010944000000⟩,
  ⟨6, 0, 6, 5, 1, 6, -552890477553920478631006721603531006355764674560000000⟩,
  ⟨6, 0, 7, 5, 2, 6, 407722767447156901372659797635922619069823451136000000⟩,
  ⟨6, 0, 8, 5, 3, 6, -102416792299584222906306445274117079880119091200000000⟩,
  ⟨6, 0, 6, 6, 0, 6, 810982301467012536682392057839587434330354352128000000⟩,
  ⟨6, 0, 7, 6, 1, 6, -1120205100774672550459838742643740921616234708992000000⟩,
  ⟨6, 0, 8, 6, 2, 6, 365233292038869535413620225243865675111862370304000000⟩,
  ⟨6, 0, 7, 7, 0, 6, 3797116947172040043656093365852673189642439229440000000⟩,
  ⟨6, 0, 8, 7, 1, 6, -682906071747626296868239647217622574027421777920000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1003. -/
namespace LaughlinFock
def collectedFourData_10_0_40 : List CollectedFourTerm := [
  ⟨6, 1, 3, 0, 3, 7, -38525607274527745191004517029859350772906459136000000⟩,
  ⟨6, 1, 4, 0, 4, 7, -468137816604305855231795295708774047830720590643200000⟩,
  ⟨6, 1, 5, 0, 5, 7, 1231149635587610837645205042364061740265518399488000000⟩,
  ⟨6, 1, 6, 0, 6, 7, 474365574974061250289089532650996556945090936832000000⟩,
  ⟨6, 1, 7, 0, 7, 7, -2173798162380462615101108622800722899203260416000000⟩,
  ⟨6, 1, 8, 0, 8, 7, 58622924881775050129800510944364672122932848230400000⟩,
  ⟨6, 1, 3, 1, 2, 7, 4149706591743229964906321552646151397806021017600000⟩,
  ⟨6, 1, 4, 1, 3, 7, 279123108108408730791247710596940886000810328064000000⟩,
  ⟨6, 1, 5, 1, 4, 7, 658847415000473721757844169969013171162982645760000000⟩,
  ⟨6, 1, 6, 1, 5, 7, -298299880383778232393053210351049965160078770176000000⟩,
  ⟨6, 1, 7, 1, 6, 7, -150457878650375946450440248312259384659792625664000000⟩,
  ⟨6, 1, 8, 1, 7, 7, 48986182055085079120255818075070228903187447808000000⟩,
  ⟨6, 1, 3, 2, 1, 7, 32485356833890328986207051421868731442088063795200000⟩,
  ⟨6, 1, 4, 2, 2, 7, -183884196331256976141048119312338736224323344793600000⟩,
  ⟨6, 1, 5, 2, 3, 7, 972057440629972633536294683645898892010581917696000000⟩,
  ⟨6, 1, 6, 2, 4, 7, 107064014560193468329515097175255599203961798656000000⟩,
  ⟨6, 1, 7, 2, 5, 7, 15259447456328690687081659235446606119315701760000000⟩,
  ⟨6, 1, 8, 2, 6, 7, 2665657591181815489228883866241953609222717440000000⟩,
  ⟨6, 1, 3, 3, 0, 7, -335104940499253706054206042786986520085746679808000000⟩,
  ⟨6, 1, 4, 3, 1, 7, 408265049708205018964927805518952007326203536998400000⟩,
  ⟨6, 1, 5, 3, 2, 7, -2640821674319457560694823905388615927665304535040000000⟩,
  ⟨6, 1, 6, 3, 3, 7, 162533075476638546977855143359913813641296609280000000⟩,
  ⟨6, 1, 7, 3, 4, 7, -61310871999643140797043574733463467512389697536000000⟩,
  ⟨6, 1, 8, 3, 5, 7, 42412660625573416451667162859662653037528219648000000⟩,
  ⟨6, 1, 4, 4, 0, 7, -681937009996039631746379597869927167106799684812800000⟩,
  ⟨6, 1, 5, 4, 1, 7, 731978210017171730844402798828458280253673963520000000⟩,
  ⟨6, 1, 6, 4, 2, 7, -494213471283718367749612545606808005967054110720000000⟩,
  ⟨6, 1, 7, 4, 3, 7, 217456722783506385254544038547053523537663885312000000⟩,
  ⟨6, 1, 8, 4, 4, 7, -60679550483042383128824379684795106817942224896000000⟩,
  ⟨6, 1, 5, 5, 0, 7, 8379705348651639201941684612732038100173637812224000000⟩,
  ⟨6, 1, 6, 5, 1, 7, 763704376785143678802274220721392767310065827840000000⟩,
  ⟨6, 1, 7, 5, 2, 7, -422388802107707424836827714856296500441517129728000000⟩,
  ⟨6, 1, 8, 5, 3, 7, 84880629033289289216998515651816859094828974080000000⟩,
  ⟨6, 1, 6, 6, 0, 7, -1120205100774672550459838742643740921616234708992000000⟩,
  ⟨6, 1, 7, 6, 1, 7, 1160499556092319543387053704732215860316147286016000000⟩,
  ⟨6, 1, 8, 6, 2, 7, -302696763646679351095667253320140026289107605913600000⟩,
  ⟨6, 1, 7, 7, 0, 7, -3933701541419910892378298997357959930673490821120000000⟩,
  ⟨6, 1, 8, 7, 1, 7, 565976493103137610442123512144438603336623587328000000⟩
]

def collectedFourData_10_0_41 : List CollectedFourTerm := [
  ⟨6, 2, 2, 0, 2, 8, 27402986926665144561661120111883052421816831180800000⟩,
  ⟨6, 2, 3, 0, 3, 8, 50243778975624265509197954060299036113216995328000000⟩,
  ⟨6, 2, 4, 0, 4, 8, 305264662280218347649374021700305135615299341516800000⟩,
  ⟨6, 2, 5, 0, 5, 8, -535207744947372718805147340682820628096491716608000000⟩,
  ⟨6, 2, 6, 0, 6, 8, -154662838490803620705840169746663742279079952384000000⟩,
  ⟨6, 2, 7, 0, 7, 8, 566998638749431574676400339892792403724704153600000⟩,
  ⟨6, 2, 8, 0, 8, 8, -12742335505472079413466754202644217109752787763200000⟩,
  ⟨6, 2, 2, 1, 1, 8, -144482791824107325027745892586675137061868850380800000⟩,
  ⟨6, 2, 3, 1, 2, 8, -5411905367864022160145668291136167136004459724800000⟩,
  ⟨6, 2, 4, 1, 3, 8, -182011404140287845207528669396954621813914075136000000⟩,
  ⟨6, 2, 5, 1, 4, 8, -286415419420977663579925509712406266203246428160000000⟩,
  ⟨6, 2, 6, 1, 5, 8, 97258124652374038916548668690368411959465869312000000⟩,
  ⟨6, 2, 7, 1, 6, 8, 39244403579065725758492891721712966308498663014400000⟩,
  ⟨6, 2, 8, 1, 7, 8, -10647683788157136813813424959298252279186980864000000⟩,
  ⟨6, 2, 2, 2, 0, 8, 152726279514317335831257094454548223896658431180800000⟩,
  ⟨6, 2, 3, 2, 1, 8, -42366290999011349171834536702384017208099051929600000⟩,
  ⟨6, 2, 4, 2, 2, 8, 119907738919492839678993346702053695641623094886400000⟩,
  ⟨6, 2, 5, 2, 3, 8, -422574686066144045190821041979964696175350644736000000⟩,
  ⟨6, 2, 6, 2, 4, 8, -34907306233184609810305794034566957235880067072000000⟩,
  ⟨6, 2, 7, 2, 5, 8, -3980169863761499491447938773268090638875754496000000⟩,
  ⟨6, 2, 8, 2, 6, 8, -579409905562507014624959026979737454531051520000000⟩,
  ⟨6, 2, 3, 3, 0, 8, 437032398843364227482985865566715692573926621184000000⟩,
  ⟨6, 2, 4, 3, 1, 8, -266222655165956197952426364614676540524018112921600000⟩,
  ⟨6, 2, 5, 3, 2, 8, 1148023093428502063664457851884692876145868144640000000⟩,
  ⟨6, 2, 6, 3, 3, 8, -52992519120367244174906749431440611281846927360000000⟩,
  ⟨6, 2, 7, 3, 4, 8, 15991908340869218840390844071711953446434871705600000⟩,
  ⟨6, 2, 8, 3, 5, 8, -9218856828803419239721410648001378469579587584000000⟩,
  ⟨6, 2, 4, 4, 0, 8, 444679459059339313991334919126472664450426155827200000⟩,
  ⟨6, 2, 5, 4, 1, 8, -318206979728278927161617031831523996167642808320000000⟩,
  ⟨6, 2, 6, 4, 2, 8, 161134075324316617002129497355597459042745712640000000⟩,
  ⟨6, 2, 7, 4, 3, 8, -56719923652038129288956844649082140894717752115200000⟩,
  ⟨6, 2, 8, 4, 4, 8, 13189365630177418066586581551048296407360339968000000⟩,
  ⟨6, 2, 5, 5, 0, 8, -3642841676864655244737983910206976432750653865984000000⟩,
  ⟨6, 2, 6, 5, 1, 8, -248999280118291132069503814933692866306852782080000000⟩,
  ⟨6, 2, 7, 5, 2, 8, 110173005002364352296972475469593335968782142668800000⟩,
  ⟨6, 2, 8, 5, 3, 8, -18449735410488394745197941798726738524126576640000000⟩,
  ⟨6, 2, 6, 6, 0, 8, 365233292038869535413620225243865675111862370304000000⟩,
  ⟨6, 2, 7, 6, 1, 8, -302696763646679351095667253320140026289107605913600000⟩,
  ⟨6, 2, 8, 6, 2, 8, 65794460555919365716017671005176315434897296588800000⟩,
  ⟨6, 2, 7, 7, 0, 8, 1026039794232405105530539570031937302723876093952000000⟩,
  ⟨6, 2, 8, 7, 1, 8, -123021196534885603962041103402119554989790593024000000⟩
]

def collectedFourData_10_0_42 : List CollectedFourTerm := [
  ⟨7, 0, 3, 0, 3, 7, 130588796802514265970903813995455142486888939520000000⟩,
  ⟨7, 0, 4, 0, 4, 7, 1586829086754785593011016525084370693074949505024000000⟩,
  ⟨7, 0, 5, 0, 5, 7, -4173181449148508014446273369099980448142102364160000000⟩,
  ⟨7, 0, 6, 0, 6, 7, -1607939084229656392165997505332033657524967178240000000⟩,
  ⟨7, 0, 7, 0, 7, 7, 7368441579491258660540834917997626078129029120000000⟩,
  ⟨7, 0, 8, 0, 8, 7, -198711915708511627287605934837563257151582896128000000⟩,
  ⟨7, 0, 3, 1, 2, 7, -14066103800458612417791517456519178996240351232000000⟩,
  ⟨7, 0, 4, 1, 3, 7, -946133063858421054270345664228790982408646164480000000⟩,
  ⟨7, 0, 5, 1, 4, 7, -2233270213971294888258521305706963377337873203200000000⟩,
  ⟨7, 0, 6, 1, 5, 7, 1011135844999578675946049119779193174431702712320000000⟩,
  ⟨7, 0, 7, 1, 6, 7, 510001392123471581253457063077898396820286996480000000⟩,
  ⟨7, 0, 8, 1, 7, 7, -166046612294468819783349687747983526848951746560000000⟩,
  ⟨7, 0, 3, 2, 1, 7, -110114387877356941725709279837822597523690225664000000⟩,
  ⟨7, 0, 4, 2, 2, 7, 623305319466648574921887379396415873254321815552000000⟩,
  ⟨7, 0, 5, 2, 3, 7, -3294946415516447572085206481783708622797899038720000000⟩,
  ⟨7, 0, 6, 2, 4, 7, -362910848948685910273947203148257875661338705920000000⟩,
  ⟨7, 0, 7, 2, 5, 7, -51724373064216095618740734039247527013987123200000000⟩,
  ⟨7, 0, 8, 2, 6, 7, -9035678919721555246320793739633831560662220800000000⟩,
  ⟨7, 0, 3, 3, 0, 7, 1135892568040307586505083267333366291349697986560000000⟩,
  ⟨7, 0, 4, 3, 1, 7, -1383880628746473554917974028076162074301209509888000000⟩,
  ⟨7, 0, 5, 3, 2, 7, 8951493549782247673274175160628261412345269452800000000⟩,
  ⟨7, 0, 6, 3, 3, 7, -550932231018716528062433564458504753071626649600000000⟩,
  ⟨7, 0, 7, 3, 4, 7, 207823148595507897974305639393683341724635627520000000⟩,
  ⟨7, 0, 8, 3, 5, 7, -143764594827010367874992938479156367262597775360000000⟩,
  ⟨7, 0, 4, 4, 0, 7, 2311536142594876029839688739922651628483322576896000000⟩,
  ⟨7, 0, 5, 4, 1, 7, -2481158909466464492004838765370189588008953446400000000⟩,
  ⟨7, 0, 6, 4, 2, 7, 1675216749177793365584312416655922486648923750400000000⟩,
  ⟨7, 0, 7, 4, 3, 7, -737104845163380778443791042781854777258897571840000000⟩,
  ⟨7, 0, 8, 4, 4, 7, 205683181880357861714706488821683845824480542720000000⟩,
  ⟨7, 0, 5, 5, 0, 7, -28404370922493783701122241852518085603989578055680000000⟩,
  ⟨7, 0, 6, 5, 1, 7, -2588699899433537145530938502333594095047199948800000000⟩,
  ⟨7, 0, 7, 5, 2, 7, 1431755379144168669580147098474173717281725480960000000⟩,
  ⟨7, 0, 8, 5, 3, 7, -287716664355518156610612247234098705901132185600000000⟩,
  ⟨7, 0, 6, 6, 0, 7, 3797116947172040043656093365852673189642439229440000000⟩,
  ⟨7, 0, 7, 6, 1, 7, -3933701541419910892378298997357959930673490821120000000⟩,
  ⟨7, 0, 8, 6, 2, 7, 1026039794232405105530539570031937302723876093952000000⟩,
  ⟨7, 0, 7, 7, 0, 7, 13333919634639137731655599048570639248207013478400000000⟩,
  ⟨7, 0, 8, 7, 1, 7, -1918469155493701703732485166231528543230057512960000000⟩
]

def collectedFourData_10_0_43 : List CollectedFourTerm := [
  ⟨7, 1, 2, 0, 2, 8, -51237569422474422526596408340143451228480733184000000⟩,
  ⟨7, 1, 3, 0, 3, 8, -93944836020994357263342490891120735403051581440000000⟩,
  ⟨7, 1, 4, 0, 4, 8, -570777899784020318858755036717383333501902782464000000⟩,
  ⟨7, 1, 5, 0, 5, 8, 1000720982007352796121140406894969777509200035840000000⟩,
  ⟨7, 1, 6, 0, 6, 8, 289185552854397970284232306778580930393349816320000000⟩,
  ⟨7, 1, 7, 0, 7, 8, -1060162973953145871770345653473739312912662528000000⟩,
  ⟨7, 1, 8, 0, 8, 8, 23825369906328694703282142640793362639865511936000000⟩,
  ⟨7, 1, 2, 1, 1, 8, 270151100544335217009799667402102850397283549184000000⟩,
  ⟨7, 1, 3, 1, 2, 8, 10119074892670485430243329334080476261388386304000000⟩,
  ⟨7, 1, 4, 1, 3, 8, 340321366436347439652933759187411659839011553280000000⟩,
  ⟨7, 1, 5, 1, 4, 8, 535533953854110031725332292424888507156974796800000000⟩,
  ⟨7, 1, 6, 1, 5, 8, -181851340772147491370934750117206657517496565760000000⟩,
  ⟨7, 1, 7, 1, 6, 8, -73378418863869824053418514419628913156908122112000000⟩,
  ⟨7, 1, 8, 1, 7, 8, 19908831060798882537063982008391579680343326720000000⟩,
  ⟨7, 1, 2, 2, 0, 8, -285564612726083741074268783644334054525248733184000000⟩,
  ⟨7, 1, 3, 2, 1, 8, 79215662951044951790951932505833458588092203008000000⟩,
  ⟨7, 1, 4, 2, 2, 8, -224201146890344883601711324840962382820039196672000000⟩,
  ⟨7, 1, 5, 2, 3, 8, 790121889684429843660130369932776530808961761280000000⟩,
  ⟨7, 1, 6, 2, 4, 8, 65268999005869804792371487387610603604997570560000000⟩,
  ⟨7, 1, 7, 2, 5, 8, 7442043827320051012293959270617887161796526080000000⟩,
  ⟨7, 1, 8, 2, 6, 8, 1083369318088463661347922091170549275924889600000000⟩,
  ⟨7, 1, 3, 3, 0, 8, -817154638490078560012185014055785639440621240320000000⟩,
  ⟨7, 1, 4, 3, 1, 8, 497777917874632473315159145748077066793326215168000000⟩,
  ⟨7, 1, 5, 3, 2, 8, -2146551144426836839523963551956443175643722547200000000⟩,
  ⟨7, 1, 6, 3, 3, 8, 99084376625364173926638306701629412608888012800000000⟩,
  ⟨7, 1, 7, 3, 4, 8, -29901357687975624889920390540002077645354303488000000⟩,
  ⟨7, 1, 8, 3, 5, 8, 17237238335578452718715905841305842004336312320000000⟩,
  ⟨7, 1, 4, 4, 0, 8, -831452962236407062484205918833680277799652294656000000⟩,
  ⟨7, 1, 5, 4, 1, 8, 594977192018379936176411065108478092046342553600000000⟩,
  ⟨7, 1, 6, 4, 2, 8, -301285345019162060185673790790765000992699187200000000⟩,
  ⟨7, 1, 7, 4, 3, 8, 106053804774501154656795224635543932091704016896000000⟩,
  ⟨7, 1, 8, 4, 4, 8, -24661218097251238802003073771001118500470128640000000⟩,
  ⟨7, 1, 5, 5, 0, 8, 6811314175821148657321187160084762220665577144320000000⟩,
  ⟨7, 1, 6, 5, 1, 8, 465573987804683416830434790386327234552424038400000000⟩,
  ⟨7, 1, 7, 5, 2, 8, -205999331656734958776253737402024749999717351424000000⟩,
  ⟨7, 1, 8, 5, 3, 8, 34496954709755288701692495810464937848025907200000000⟩,
  ⟨7, 1, 6, 6, 0, 8, -682906071747626296868239647217622574027421777920000000⟩,
  ⟨7, 1, 7, 6, 1, 8, 565976493103137610442123512144438603336623587328000000⟩,
  ⟨7, 1, 8, 6, 2, 8, -123021196534885603962041103402119554989790593024000000⟩,
  ⟨7, 1, 7, 7, 0, 8, -1918469155493701703732485166231528543230057512960000000⟩,
  ⟨7, 1, 8, 7, 1, 8, 230022629093709647669150557971612106499838443520000000⟩
]

def collectedFourData_10_0 : List (List CollectedFourTerm) := [
  collectedFourData_10_0_0,
  collectedFourData_10_0_1,
  collectedFourData_10_0_2,
  collectedFourData_10_0_3,
  collectedFourData_10_0_4,
  collectedFourData_10_0_5,
  collectedFourData_10_0_6,
  collectedFourData_10_0_7,
  collectedFourData_10_0_8,
  collectedFourData_10_0_9,
  collectedFourData_10_0_10,
  collectedFourData_10_0_11,
  collectedFourData_10_0_12,
  collectedFourData_10_0_13,
  collectedFourData_10_0_14,
  collectedFourData_10_0_15,
  collectedFourData_10_0_16,
  collectedFourData_10_0_17,
  collectedFourData_10_0_18,
  collectedFourData_10_0_19,
  collectedFourData_10_0_20,
  collectedFourData_10_0_21,
  collectedFourData_10_0_22,
  collectedFourData_10_0_23,
  collectedFourData_10_0_24,
  collectedFourData_10_0_25,
  collectedFourData_10_0_26,
  collectedFourData_10_0_27,
  collectedFourData_10_0_28,
  collectedFourData_10_0_29,
  collectedFourData_10_0_30,
  collectedFourData_10_0_31,
  collectedFourData_10_0_32,
  collectedFourData_10_0_33,
  collectedFourData_10_0_34,
  collectedFourData_10_0_35,
  collectedFourData_10_0_36,
  collectedFourData_10_0_37,
  collectedFourData_10_0_38,
  collectedFourData_10_0_39,
  collectedFourData_10_0_40,
  collectedFourData_10_0_41,
  collectedFourData_10_0_42,
  collectedFourData_10_0_43
]

def collectedFourData_10_1_0 : List CollectedFourTerm := [

]

def collectedFourData_10_1_1 : List CollectedFourTerm := [
  ⟨0, 2, 8, 1, 8, 1, -71821454090837103110257157637922310291793641472000000⟩,
  ⟨0, 2, 8, 2, 7, 1, -30838505014981829971544030689925013690944323584000000⟩,
  ⟨0, 2, 8, 3, 6, 1, 1655994705926514365409294010316987760409313280000000⟩,
  ⟨0, 2, 8, 4, 5, 1, 22539964173521803300085276851997384862288838656000000⟩,
  ⟨0, 2, 8, 5, 4, 1, 11283557899503119482351002190422054580852359168000000⟩,
  ⟨0, 2, 8, 6, 3, 1, -59908931096597619089274501323259834772777598976000000⟩,
  ⟨0, 2, 8, 7, 2, 1, 23563777749833530675844192329001860227183673344000000⟩
]

def collectedFourData_10_1_2 : List CollectedFourTerm := [
  ⟨0, 3, 7, 0, 8, 2, -59758950892437995811592191312328261029832163328000000⟩,
  ⟨0, 3, 7, 1, 7, 2, 4727508290973887038058176422234107098158858240000000⟩,
  ⟨0, 3, 8, 1, 8, 2, 68319216536856617967971449697165181962838815539200000⟩,
  ⟨0, 3, 7, 2, 6, 2, 2965079809650524249543286340392774066089282764800000⟩,
  ⟨0, 3, 8, 2, 7, 2, 29334723565006092389153157449310880485450606182400000⟩,
  ⟨0, 3, 7, 3, 5, 2, 7111703583231803019824149737547895111802893107200000⟩,
  ⟨0, 3, 8, 3, 6, 2, -1575243251897840978792958784844377255374225408000000⟩,
  ⟨0, 3, 7, 4, 4, 2, -3676785488009098727411419561167070960119132979200000⟩,
  ⟨0, 3, 8, 4, 5, 2, -21440845393581174392492549547360659013853878681600000⟩,
  ⟨0, 3, 7, 5, 3, 2, -4194050760439917620923952247766944791285622374400000⟩,
  ⟨0, 3, 8, 5, 4, 2, -10733336510666122824875037160044071881177615564800000⟩,
  ⟨0, 3, 7, 6, 2, 2, -29683379782966650120397092102948926654612137574400000⟩,
  ⟨0, 3, 8, 6, 3, 2, 56987585226323719135975243036695141167518030233600000⟩,
  ⟨0, 3, 7, 7, 1, 2, 153568030105498116088661307828197845221917274931200000⟩,
  ⟨0, 3, 8, 7, 2, 2, -22414734634600288298506910994836410911150204518400000⟩
]

def collectedFourData_10_1_3 : List CollectedFourTerm := [
  ⟨0, 4, 6, 0, 7, 3, -7457731428010067554426376679105246454379603558400000⟩,
  ⟨0, 4, 7, 0, 8, 3, -21875770995296472956431072458786893832382316544000000⟩,
  ⟨0, 4, 6, 1, 6, 3, 2748213688397789966811642217453542273563649638400000⟩,
  ⟨0, 4, 7, 1, 7, 3, 1730584074975734568199980062829994736898539520000000⟩,
  ⟨0, 4, 8, 1, 8, 3, 12504700243386203280518294734779027073364970700800000⟩,
  ⟨0, 4, 6, 2, 5, 3, 49374508204002039818412679586577934515280281600000⟩,
  ⟨0, 4, 7, 2, 6, 3, 1085417430025533741321892308754157746950399590400000⟩,
  ⟨0, 4, 8, 2, 7, 3, 5369234945853145653235577657752586019854195097600000⟩,
  ⟨0, 4, 6, 3, 4, 3, -799507214512309626441208002278672670749255270400000⟩,
  ⟨0, 4, 7, 3, 5, 3, 2603358938700760957428199949953612411511085465600000⟩,
  ⟨0, 4, 8, 3, 6, 3, -288322168694262270805220373604278810225672192000000⟩,
  ⟨0, 4, 6, 4, 3, 3, 1009465616340567478172026025209479033206813491200000⟩,
  ⟨0, 4, 7, 4, 4, 3, -1345949286815450166232319209536136759006042521600000⟩,
  ⟨0, 4, 8, 4, 5, 3, -3924391382135956915810490276248628149940020838400000⟩,
  ⟨0, 4, 6, 5, 2, 3, -2191283884392581917634213888076841152196431052800000⟩,
  ⟨0, 4, 7, 5, 3, 3, -1535302956425271403941765039302245699101602611200000⟩,
  ⟨0, 4, 8, 5, 4, 3, -1964559350660376418232390203747541779119026995200000⟩,
  ⟨0, 4, 6, 6, 1, 3, 4103842100877123980339123731964914523522570649600000⟩,
  ⟨0, 4, 7, 6, 2, 3, -10866101375631095010260707340823075604315452211200000⟩,
  ⟨0, 4, 8, 6, 3, 3, 10430632945932047674861163206909398155585283686400000⟩,
  ⟨0, 4, 6, 7, 0, 3, 1217744959141844593939359486117734847282885427200000⟩,
  ⟨0, 4, 7, 7, 1, 3, 56216165254195888552096514251328943293986347417600000⟩,
  ⟨0, 4, 8, 7, 2, 3, -4102645666165005586184404726923794815638935961600000⟩
]

def collectedFourData_10_1_4 : List CollectedFourTerm := [
  ⟨0, 5, 5, 0, 6, 4, 319049947695547491666948391203688417990899086131200000⟩,
  ⟨0, 5, 6, 0, 7, 4, 439331265146748978460788413776534373382879392563200000⟩,
  ⟨0, 5, 7, 0, 8, 4, 644345417919438489831634242030076740619632377856000000⟩,
  ⟨0, 5, 5, 1, 5, 4, -104579090057856694817286802409440120427205623808000000⟩,
  ⟨0, 5, 6, 1, 6, 4, -161895907391180532175759870353928557459106116403200000⟩,
  ⟨0, 5, 7, 1, 7, 4, -50973925411576204575404918300461660474158612480000000⟩,
  ⟨0, 5, 8, 1, 8, 4, -245548566220116427286835539525708288497279618252800000⟩,
  ⟨0, 5, 5, 2, 4, 4, 78559755044625612243191090080679173082212781260800000⟩,
  ⟨0, 5, 6, 2, 5, 4, -2908627826659443774219239867363299503056407756800000⟩,
  ⟨0, 5, 7, 2, 6, 4, -31970701636857529805466873684572480474321623449600000⟩,
  ⟨0, 5, 8, 2, 7, 4, -105432990554931274129765703201553693900770220441600000⟩,
  ⟨0, 5, 5, 3, 3, 4, -23458380130554369869731194180832709004455470694400000⟩,
  ⟨0, 5, 6, 3, 4, 4, 47098574068571572835133363753081387082474271539200000⟩,
  ⟨0, 5, 7, 3, 5, 4, -76681292911327340342169649958238849558238357094400000⟩,
  ⟨0, 5, 8, 3, 6, 4, 5661638724190575165977373385211134326626844672000000⟩,
  ⟨0, 5, 5, 4, 2, 4, -48448237362729580644532747956432040299790860288000000⟩,
  ⟨0, 5, 6, 4, 3, 4, -59467119542997511726680745659541089976411855257600000⟩,
  ⟨0, 5, 7, 4, 4, 4, 39644602967270999557060538547766780028632065638400000⟩,
  ⟨0, 5, 8, 4, 5, 4, 77061317617728032919871821943916188002003871334400000⟩,
  ⟨0, 5, 5, 5, 1, 4, -16356867533270341127274107657095141721663707545600000⟩,
  ⟨0, 5, 6, 5, 2, 4, 129087448444459569928292150459004222321956644454400000⟩,
  ⟨0, 5, 7, 5, 3, 4, 45221968419009950105208187102570692495329250508800000⟩,
  ⟨0, 5, 8, 5, 4, 4, 38577072814209943625263297217646736710034469683200000⟩,
  ⟨0, 5, 5, 6, 0, 4, 868530401107110443506212556194925609449052490956800000⟩,
  ⟨0, 5, 6, 6, 1, 4, -241755305825208008444395200505493963320601660620800000⟩,
  ⟨0, 5, 7, 6, 2, 4, 320058325420457472372299847721612768389836360908800000⟩,
  ⟨0, 5, 8, 6, 3, 4, -204821140434499330369067339263266641738436339302400000⟩,
  ⟨0, 5, 6, 7, 0, 4, -71736752481661037768421193516365164374461618585600000⟩,
  ⟨0, 5, 7, 7, 1, 4, -1655833227653156693774873508286222275092689610342400000⟩,
  ⟨0, 5, 8, 7, 2, 4, 80561608149608356044014789928465773174399277465600000⟩
]

def collectedFourData_10_1_5 : List CollectedFourTerm := [
  ⟨0, 6, 4, 0, 5, 5, 319049947695547491666948391203688417990899086131200000⟩,
  ⟨0, 6, 5, 0, 6, 5, 556545034187044471198146433947542465747833847808000000⟩,
  ⟨0, 6, 6, 0, 7, 5, 383180808752013377724146650532194672934695993344000000⟩,
  ⟨0, 6, 7, 0, 8, 5, 374661548799708414800720917899349659263623495680000000⟩,
  ⟨0, 6, 4, 1, 4, 5, 98182255570566771770447077405437769477153986969600000⟩,
  ⟨0, 6, 5, 1, 5, 5, -182425898113733210977064412650571694036714782720000000⟩,
  ⟨0, 6, 6, 1, 6, 5, -141204165624479399366522774314055978850812166144000000⟩,
  ⟨0, 6, 7, 1, 7, 5, -29639335226078607141499087487839807151171174400000000⟩,
  ⟨0, 6, 8, 1, 8, 5, -107082634058257828318312844947588597695998066688000000⟩,
  ⟨0, 6, 4, 2, 3, 5, 154157029435069959229951926148407651263125546598400000⟩,
  ⟨0, 6, 5, 2, 4, 5, 137038234523575709722952627699937844348921577472000000⟩,
  ⟨0, 6, 6, 2, 5, 5, -2536879233044550577971803936855234042507821056000000⟩,
  ⟨0, 6, 7, 2, 6, 5, -18589707101752107091347780705731467175408959488000000⟩,
  ⟨0, 6, 8, 2, 7, 5, -45978856724990028704092526820823344601613991936000000⟩,
  ⟨0, 6, 4, 3, 2, 5, -411262730782341956940361388539909446245198227046400000⟩,
  ⟨0, 6, 5, 3, 3, 5, -40920379602100354319703144579942504633515114496000000⟩,
  ⟨0, 6, 6, 3, 4, 5, 41078955982414694819044158893637489601768587264000000⟩,
  ⟨0, 6, 7, 3, 5, 5, -44587159568680307082246158099986293889362296832000000⟩,
  ⟨0, 6, 8, 3, 6, 5, 2469015384635112217107949484706367055981445120000000⟩,
  ⟨0, 6, 4, 4, 1, 5, 5279867205243499130732348572950362653993205760000000⟩,
  ⟨0, 6, 5, 4, 2, 5, -84512240525650683834280962844770687990544465920000000⟩,
  ⟨0, 6, 6, 4, 3, 5, -51866690965021719547357579618003255887598190592000000⟩,
  ⟨0, 6, 7, 4, 4, 5, 23051779272719767791060788040870536743225393152000000⟩,
  ⟨0, 6, 8, 4, 5, 5, 33606096755250828545395103682743613849310593024000000⟩,
  ⟨0, 6, 4, 5, 0, 5, 1694671685459190136644044124846551090557848492441600000⟩,
  ⟨0, 6, 5, 5, 1, 5, -28532627778969987071522002590556110832590127104000000⟩,
  ⟨0, 6, 6, 5, 2, 5, 112588920522557255701519436579138277248700776448000000⟩,
  ⟨0, 6, 7, 5, 3, 5, 26294798188129767788560443754516487386655883264000000⟩,
  ⟨0, 6, 8, 5, 4, 5, 16823289318251313011014437291404929038519631872000000⟩,
  ⟨0, 6, 5, 6, 0, 5, 1515048929698946937022109148483524419512919130112000000⟩,
  ⟨0, 6, 6, 6, 1, 5, -210856820252140517672128829942750796220974759936000000⟩,
  ⟨0, 6, 7, 6, 2, 5, 186101343430771923024810084232285619703213195264000000⟩,
  ⟨0, 6, 8, 6, 3, 5, -89321585404336587914553346671493849940496482304000000⟩,
  ⟨0, 6, 6, 7, 0, 5, -62568155316658527132189283533488353802402660352000000⟩,
  ⟨0, 6, 7, 7, 1, 5, -962801976042167868446248511000296563924661174272000000⟩,
  ⟨0, 6, 8, 7, 2, 5, 35132557837442308897882491248078872836336254976000000⟩
]

def collectedFourData_10_1_6 : List CollectedFourTerm := [
  ⟨0, 7, 3, 0, 4, 6, -7457731428010067554426376679105246454379603558400000⟩,
  ⟨0, 7, 4, 0, 5, 6, 439331265146748978460788413776534373382879392563200000⟩,
  ⟨0, 7, 5, 0, 6, 6, 383180808752013377724146650532194672934695993344000000⟩,
  ⟨0, 7, 6, 0, 7, 6, 175879785913246857032046102282667363523497033728000000⟩,
  ⟨0, 7, 7, 0, 8, 6, 128977087619746235183318031551692119789923205120000000⟩,
  ⟨0, 7, 3, 1, 3, 6, 35798397629754409893451483455205999395689044377600000⟩,
  ⟨0, 7, 4, 1, 4, 6, 135196808105856671894156955844452918157750409625600000⟩,
  ⟨0, 7, 5, 1, 5, 6, -125600084238717476660877005192886311776640040960000000⟩,
  ⟨0, 7, 6, 1, 6, 6, -64812636366047117790574479616380853173331427328000000⟩,
  ⟨0, 7, 7, 1, 7, 6, -10203329241263059502989456686536183271496089600000000⟩,
  ⟨0, 7, 8, 1, 8, 6, -29490522995448399860115940807419808464611416473600000⟩,
  ⟨0, 7, 3, 2, 2, 6, -27937555473975275414139855678259908537976514150400000⟩,
  ⟨0, 7, 4, 2, 3, 6, 212273981745332405885081892997584833441266296422400000⟩,
  ⟨0, 7, 5, 2, 4, 6, 94350714334186371794015708391828220245700509696000000⟩,
  ⟨0, 7, 6, 2, 5, 6, -1164426208736355477857756215553629625172099072000000⟩,
  ⟨0, 7, 7, 2, 6, 6, -6399499199662643249808074256751586264368545792000000⟩,
  ⟨0, 7, 8, 2, 7, 6, -12662562361092577919451118282809301780491612979200000⟩,
  ⟨0, 7, 3, 3, 1, 6, -625946527720038255238678570641545376795564441600000⟩,
  ⟨0, 7, 4, 3, 2, 6, -566308119237577950076145780494483468484839106150400000⟩,
  ⟨0, 7, 5, 3, 3, 6, -28173648469033828389217107891596087899642134528000000⟩,
  ⟨0, 7, 6, 3, 4, 6, 18855218786290076875421962075625048006373408768000000⟩,
  ⟨0, 7, 7, 3, 5, 6, -15349111764547753601112738490842422850342617088000000⟩,
  ⟨0, 7, 8, 3, 6, 6, 679966043206261695698753718653830407508721664000000⟩,
  ⟨0, 7, 3, 4, 0, 6, 120021089212769463978440105534641714720178543001600000⟩,
  ⟨0, 7, 4, 4, 1, 6, 7270368654941571087208264757467983828599439360000000⟩,
  ⟨0, 7, 5, 4, 2, 6, -58186609680861918490377965784233528321963458560000000⟩,
  ⟨0, 7, 6, 4, 3, 6, -23806783363360764908012059670072607024196091904000000⟩,
  ⟨0, 7, 7, 4, 4, 6, 7935565751472550174525413061295282757952339968000000⟩,
  ⟨0, 7, 8, 4, 5, 6, 9255108242937000487029933592935061739927293132800000⟩,
  ⟨0, 7, 4, 5, 0, 6, 2333560186919753704297025102952715332114026437017600000⟩,
  ⟨0, 7, 5, 5, 1, 6, -19644691294633763545842344487703716395086774272000000⟩,
  ⟨0, 7, 6, 5, 2, 6, 51678254195988325944594998051757923813950488576000000⟩,
  ⟨0, 7, 7, 5, 3, 6, 9051973709922903705541908983738433464042520576000000⟩,
  ⟨0, 7, 8, 5, 4, 6, 4633128470009953034352241790253545331913811558400000⟩,
  ⟨0, 7, 5, 6, 0, 6, 1043109970478699472660846173627852112583999881216000000⟩,
  ⟨0, 7, 6, 6, 1, 6, -96783167521041950782306537291727655343994437632000000⟩,
  ⟨0, 7, 7, 6, 2, 6, 64065312692802908318824670970960022590587928576000000⟩,
  ⟨0, 7, 8, 6, 3, 6, -24599135905859432526026668391348083280250195148800000⟩,
  ⟨0, 7, 6, 7, 0, 6, -28718749767038947961433167392695704766092673024000000⟩,
  ⟨0, 7, 7, 7, 1, 6, -331444193358739846584329959762499138490936066048000000⟩,
  ⟨0, 7, 8, 7, 2, 6, 9675495134256222929037688037805054803288732467200000⟩
]

def collectedFourData_10_1_7 : List CollectedFourTerm := [
  ⟨0, 8, 2, 0, 3, 7, -59758950892437995811592191312328261029832163328000000⟩,
  ⟨0, 8, 3, 0, 4, 7, -21875770995296472956431072458786893832382316544000000⟩,
  ⟨0, 8, 4, 0, 5, 7, 644345417919438489831634242030076740619632377856000000⟩,
  ⟨0, 8, 5, 0, 6, 7, 374661548799708414800720917899349659263623495680000000⟩,
  ⟨0, 8, 6, 0, 7, 7, 128977087619746235183318031551692119789923205120000000⟩,
  ⟨0, 8, 7, 0, 8, 7, 75665723810134709919425759138046735000891555840000000⟩,
  ⟨0, 8, 2, 1, 2, 7, 57321579620308519101743254388388733976051712000000000⟩,
  ⟨0, 8, 3, 1, 3, 7, 105007475276704796512386656555326278691996041216000000⟩,
  ⟨0, 8, 4, 1, 4, 7, 198286465661040559429388542538304727905309032448000000⟩,
  ⟨0, 8, 5, 1, 5, 7, -122807617227788622868806075476752543903855411200000000⟩,
  ⟨0, 8, 6, 1, 6, 7, -47528742635459416254227061091648614637366149120000000⟩,
  ⟨0, 8, 7, 1, 7, 7, -5985887156868033279954772664833386990482227200000000⟩,
  ⟨0, 8, 8, 1, 8, 7, -14417430059158799634178135557913115519505924096000000⟩,
  ⟨0, 8, 2, 2, 1, 7, 79432523991935027999686078820741145760559529984000000⟩,
  ⟨0, 8, 3, 2, 2, 7, -81949259183787478742599978229047951631019147264000000⟩,
  ⟨0, 8, 4, 2, 3, 7, 311331740606787571068149300901760466479472443392000000⟩,
  ⟨0, 8, 5, 2, 4, 7, 92253014648451846318304778107381982973520773120000000⟩,
  ⟨0, 8, 6, 2, 5, 7, -853903138277622310613399354709638340547706880000000⟩,
  ⟨0, 8, 7, 2, 6, 7, -3754331470039472136232038906915330035804012544000000⟩,
  ⟨0, 8, 8, 2, 7, 7, -6190517789018720247275571452075714660335091712000000⟩,
  ⟨0, 8, 2, 3, 0, 7, -137558249562460946508878114441955578221833486336000000⟩,
  ⟨0, 8, 3, 3, 1, 7, -1836089570653558219044698773800901702588563456000000⟩,
  ⟨0, 8, 4, 3, 2, 7, -830576083947547362443568507087137362138084933632000000⟩,
  ⟨0, 8, 5, 3, 3, 7, -27547263666793137426317708675299902797025116160000000⟩,
  ⟨0, 8, 6, 3, 4, 7, 13827007992199609055274645232148213832320286720000000⟩,
  ⟨0, 8, 7, 3, 5, 7, -9004712952824890515065701667426170883713007616000000⟩,
  ⟨0, 8, 8, 3, 6, 7, 332424178168772741105882081875402104546263040000000⟩,
  ⟨0, 8, 3, 4, 0, 7, 352057980039804708826657636447064046182445613056000000⟩,
  ⟨0, 8, 4, 4, 1, 7, 10663089793602362843432676781443776122768588800000000⟩,
  ⟨0, 8, 5, 4, 2, 7, -56892946631219528044687954759790108704191283200000000⟩,
  ⟨0, 8, 6, 4, 3, 7, -17458115313575857562986651250721718022606684160000000⟩,
  ⟨0, 8, 7, 4, 4, 7, 4655480578057011944339350602407713564079947776000000⟩,
  ⟨0, 8, 8, 4, 5, 7, 4524669698230946270422453538278122147815620608000000⟩,
  ⟨0, 8, 4, 5, 0, 7, 3422517205504872949693151125036174163352703991808000000⟩,
  ⟨0, 8, 5, 5, 1, 7, -19207930820206981614895388760691945705926819840000000⟩,
  ⟨0, 8, 6, 5, 2, 7, 37896968573518653120610339957249152675521495040000000⟩,
  ⟨0, 8, 7, 5, 3, 7, 5310432692440217776756203668422640109493420032000000⟩,
  ⟨0, 8, 8, 5, 4, 7, 2265060056133136861666628853288789804186599424000000⟩,
  ⟨0, 8, 5, 6, 0, 7, 1019918503697542460005714574512378063695139307520000000⟩,
  ⟨0, 8, 6, 6, 1, 7, -70973540322792884268954547559254948884806369280000000⟩,
  ⟨0, 8, 7, 6, 2, 7, 37584569053964192078132633283501564102319276032000000⟩,
  ⟨0, 8, 8, 6, 3, 7, -12026111625528254004494380016564178053253562368000000⟩,
  ⟨0, 8, 6, 7, 0, 7, -21060184294629437119896557750792230364208168960000000⟩,
  ⟨0, 8, 7, 7, 1, 7, -194445116229432795058392870286045023388708110336000000⟩,
  ⟨0, 8, 8, 7, 2, 7, 4730189912447477015578845730757387651899195392000000⟩
]

def collectedFourData_10_1_8 : List CollectedFourTerm := [

]

def collectedFourData_10_1_9 : List CollectedFourTerm := [
  ⟨1, 1, 8, 1, 8, 1, 70993500039696456769917706874495824031300085350400000⟩,
  ⟨1, 1, 8, 2, 7, 1, 30483000305678919914152270691593694684474297548800000⟩,
  ⟨1, 1, 8, 3, 6, 1, -1636904483613482100989894414561073601336836096000000⟩,
  ⟨1, 1, 8, 4, 5, 1, -22280124618805613134572321967673622015014810419200000⟩,
  ⟨1, 1, 8, 5, 4, 1, -11153481620869747656535490120069611448253913497600000⟩,
  ⟨1, 1, 8, 6, 3, 1, 59218304001548843297146685157705890352493441843200000⟩,
  ⟨1, 1, 8, 7, 2, 1, -23292135724548476982223805214617009717374667980800000⟩
]

def collectedFourData_10_1_10 : List CollectedFourTerm := [
  ⟨1, 2, 7, 0, 8, 2, 57321579620308519101743254388388733976051712000000000⟩,
  ⟨1, 2, 7, 1, 7, 2, -4534688759755647838836990051510777764904960000000000⟩,
  ⟨1, 2, 8, 1, 8, 2, -65532700153377083929535023243088130061683916800000000⟩,
  ⟨1, 2, 7, 2, 6, 2, -2844143945822837099624412615096181571400499200000000⟩,
  ⟨1, 2, 8, 2, 7, 2, -28138256568423441102594602132985011638999449600000000⟩,
  ⟨1, 2, 7, 3, 5, 2, -6821640559185928824576235606997934411664588800000000⟩,
  ⟨1, 2, 8, 3, 6, 2, 1510994255028696383795939464557677386924032000000000⟩,
  ⟨1, 2, 7, 4, 4, 2, 3526821487831345201988223912055078510185676800000000⟩,
  ⟨1, 2, 8, 4, 5, 2, 20566343752704855680992206898047530383599206400000000⟩,
  ⟨1, 2, 7, 5, 3, 2, 4022989209246544690555329550499914341521817600000000⟩,
  ⟨1, 2, 8, 5, 4, 2, 10295558978187611359101133146760068264571699200000000⟩,
  ⟨1, 2, 7, 6, 2, 2, 28472692244744371212821487410838720162142617600000000⟩,
  ⟨1, 2, 8, 6, 3, 2, -54663248854544336750428255482650833751271014400000000⟩,
  ⟨1, 2, 7, 7, 1, 2, -147304494696880013964735347636728251730939084800000000⟩,
  ⟨1, 2, 8, 7, 2, 2, 21500511251242771775431311590861295817693593600000000⟩
]

def collectedFourData_10_1_11 : List CollectedFourTerm := [
  ⟨1, 3, 6, 0, 7, 3, 35798397629754409893451483455205999395689044377600000⟩,
  ⟨1, 3, 7, 0, 8, 3, 105007475276704796512386656555326278691996041216000000⟩,
  ⟨1, 3, 6, 1, 6, 3, -13191899887852231004541841458216734010457561497600000⟩,
  ⟨1, 3, 7, 1, 7, 3, -8307102159112296762007027960600000720042721280000000⟩,
  ⟨1, 3, 8, 1, 8, 3, -60024718759960921175697507179048210728999924531200000⟩,
  ⟨1, 3, 6, 2, 5, 3, -237006158578180728717327622369795712013985382400000⟩,
  ⟨1, 3, 7, 2, 6, 3, -5210190944713078538824710410984595073904777625600000⟩,
  ⟨1, 3, 8, 2, 7, 3, -25773254161086199289635459104110073140820207206400000⟩,
  ⟨1, 3, 6, 3, 4, 3, 3837772578598465786787735749359242739057269145600000⟩,
  ⟨1, 3, 7, 3, 5, 3, -12496572095712034968006618078630554810741843558400000⟩,
  ⟨1, 3, 8, 3, 6, 3, 1383996157547924524296785397504206945793343488000000⟩,
  ⟨1, 3, 6, 4, 3, 3, -4845609134112674817751262411842417655699786956800000⟩,
  ⟨1, 3, 7, 4, 4, 3, 6460788810111439334403064188791910927341872742400000⟩,
  ⟨1, 3, 8, 4, 5, 3, 18837755758384870408300145143012865025116838297600000⟩,
  ⟨1, 3, 6, 5, 2, 3, 10518540734590334577792726585361278114064446259200000⟩,
  ⟨1, 3, 7, 5, 3, 3, 7369719095786024708829054128379628577962642636800000⟩,
  ⟨1, 3, 8, 5, 4, 3, 9430223853067579584231582559565332663346449612800000⟩,
  ⟨1, 3, 6, 6, 1, 3, -19699150171210438866138466172175066112201221734400000⟩,
  ⟨1, 3, 7, 6, 2, 3, 52159161466861314971198197589383300531069177036800000⟩,
  ⟨1, 3, 8, 6, 3, 3, -50068837867512973493196212804344067168193321369600000⟩,
  ⟨1, 3, 6, 7, 0, 3, -5845385916588405936141481138830530728533216460800000⟩,
  ⟨1, 3, 7, 7, 1, 3, -269847292895430292233976899380287785671649027686400000⟩,
  ⟨1, 3, 8, 7, 2, 3, 19693407078156485408301854097151678196033676902400000⟩
]

def collectedFourData_10_1_12 : List CollectedFourTerm := [
  ⟨1, 4, 5, 0, 6, 4, 98182255570566771770447077405437769477153986969600000⟩,
  ⟨1, 4, 6, 0, 7, 4, 135196808105856671894156955844452918157750409625600000⟩,
  ⟨1, 4, 7, 0, 8, 4, 198286465661040559429388542538304727905309032448000000⟩,
  ⟨1, 4, 5, 1, 5, 4, -32182456137544438867622066636575411184037003264000000⟩,
  ⟨1, 4, 6, 1, 6, 4, -49820742708529597029668616474096941390443944345600000⟩,
  ⟨1, 4, 7, 1, 7, 4, -15686368257831958959723967958049406414844067840000000⟩,
  ⟨1, 4, 8, 1, 8, 4, -75563441579420628088525319690586318547894822502400000⟩,
  ⟨1, 4, 5, 2, 4, 4, 24175443384534977094453537663814864399222859366400000⟩,
  ⟨1, 4, 6, 2, 5, 4, -895081295889286406756655532357708606293304934400000⟩,
  ⟨1, 4, 7, 2, 6, 4, -9838445740400568559164843359793989168814410956800000⟩,
  ⟨1, 4, 8, 2, 7, 4, -32445229654484840959336414674891306841756454092800000⟩,
  ⟨1, 4, 5, 3, 3, 4, -7218921958412021285356096365766680561587532595200000⟩,
  ⟨1, 4, 6, 3, 4, 4, 14493794058297213599475580649494467198230043033600000⟩,
  ⟨1, 4, 7, 3, 5, 4, -23597378255287200577925789259993355481204863795200000⟩,
  ⟨1, 4, 8, 3, 6, 4, 1742274099029586329811569138256644431807512576000000⟩,
  ⟨1, 4, 5, 4, 2, 4, -14909130238222510761846432731276007698652463104000000⟩,
  ⟨1, 4, 6, 4, 3, 4, -18300005911887847376278971256406260753221078220800000⟩,
  ⟨1, 4, 7, 4, 4, 4, 12199959813942860861053767786567375142578762547200000⟩,
  ⟨1, 4, 8, 4, 5, 4, 23714324467366091022916817117717251409969361715200000⟩,
  ⟨1, 4, 5, 5, 1, 4, -5033550890965611176988674429249303711228677324800000⟩,
  ⟨1, 4, 6, 5, 2, 4, 39724491245554168116938682966530693234777338675200000⟩,
  ⟨1, 4, 7, 5, 3, 4, 13916300230696752267321772768651600913204930150400000⟩,
  ⟨1, 4, 8, 5, 4, 4, 11871445363230134508226462251782959956823218585600000⟩,
  ⟨1, 4, 5, 6, 0, 4, 267275623858361892356820214108672033499963090534400000⟩,
  ⟨1, 4, 6, 6, 1, 4, -74396129488543877616471346114474758685187270246400000⟩,
  ⟨1, 4, 7, 6, 2, 4, 98492566856350944505075004707238628571134453350400000⟩,
  ⟨1, 4, 8, 6, 3, 4, -63030261254218045130077632599851601306970174259200000⟩,
  ⟨1, 4, 6, 7, 0, 4, -22075779096124348635600190295875943667319229644800000⟩,
  ⟨1, 4, 7, 7, 1, 4, -509554827743817550458538946087463184089679606579200000⟩,
  ⟨1, 4, 8, 7, 2, 4, 24791480010109673260841995756289155050005908684800000⟩
]

def collectedFourData_10_1_13 : List CollectedFourTerm := [
  ⟨1, 5, 4, 0, 5, 5, -104579090057856694817286802409440120427205623808000000⟩,
  ⟨1, 5, 5, 0, 6, 5, -182425898113733210977064412650571694036714782720000000⟩,
  ⟨1, 5, 6, 0, 7, 5, -125600084238717476660877005192886311776640040960000000⟩,
  ⟨1, 5, 7, 0, 8, 5, -122807617227788622868806075476752543903855411200000000⟩,
  ⟨1, 5, 4, 1, 4, 5, -32182456137544438867622066636575411184037003264000000⟩,
  ⟨1, 5, 5, 1, 5, 5, 59796074456425111460678458952018317263293644800000000⟩,
  ⟨1, 5, 6, 1, 6, 5, 46284298932022751914862438045208700477463592960000000⟩,
  ⟨1, 5, 7, 1, 7, 5, 9715264742249435176167033145417087315869696000000000⟩,
  ⟨1, 5, 8, 1, 8, 5, 35099847254942334260212392345414692312627281920000000⟩,
  ⟨1, 5, 4, 2, 3, 5, -50530025097279876427275652912549489889935097856000000⟩,
  ⟨1, 5, 5, 2, 4, 5, -44918778307672205949044392780983309724790292480000000⟩,
  ⟨1, 5, 6, 2, 5, 5, 831545416931516204025489389706185840567255040000000⟩,
  ⟨1, 5, 7, 2, 6, 5, 6093386528301388685726103080273871393175633920000000⟩,
  ⟨1, 5, 8, 2, 7, 5, 15071079098838937837597517547918590818375434240000000⟩,
  ⟨1, 5, 4, 3, 2, 5, 134804855699171869739117033209050426202103218176000000⟩,
  ⟨1, 5, 5, 3, 3, 5, 13412997226670463860418681537623794412830064640000000⟩,
  ⟨1, 5, 6, 3, 4, 5, -13464975839040484894015684254121156360808693760000000⟩,
  ⟨1, 5, 7, 3, 5, 5, 14614904686982080594217275533153073143616634880000000⟩,
  ⟨1, 5, 8, 3, 6, 5, -809300813646842374761371821780087237037260800000000⟩,
  ⟨1, 5, 4, 4, 1, 5, -1730649736628650653909155291959141427734118400000000⟩,
  ⟨1, 5, 5, 4, 2, 5, 27701660121747172297737274370651139208957132800000000⟩,
  ⟨1, 5, 6, 4, 3, 5, 17001009981703644421119223329064198914472673280000000⟩,
  ⟨1, 5, 7, 4, 4, 5, -7555977106305722017856409388461508209074503680000000⟩,
  ⟨1, 5, 8, 4, 5, 5, -11015501003667673270092724569661334135934812160000000⟩,
  ⟨1, 5, 4, 5, 0, 5, -555484255967517080482798484767403545944070815744000000⟩,
  ⟨1, 5, 5, 5, 1, 5, 9352505059588975540544711681737672011137679360000000⟩,
  ⟨1, 5, 6, 5, 2, 5, -36904713333728917054735117253102187594456760320000000⟩,
  ⟨1, 5, 7, 5, 3, 5, -8618982976275742936960936722713819838425333760000000⟩,
  ⟨1, 5, 8, 5, 4, 5, -5514385134335301656181154859081569111879188480000000⟩,
  ⟨1, 5, 5, 6, 0, 5, -496607003403237715095269296323509143201728430080000000⟩,
  ⟨1, 5, 6, 6, 1, 5, 69115242154824652809015273696814795006924554240000000⟩,
  ⟨1, 5, 7, 6, 2, 5, -61000822269705142499619978975957332967303413760000000⟩,
  ⟨1, 5, 8, 6, 3, 5, 29278080725543447639782038446207749624021647360000000⟩,
  ⟨1, 5, 6, 7, 0, 5, 20508766094074845471587747331233648891060551680000000⟩,
  ⟨1, 5, 7, 7, 1, 5, 315589942225843606537875678992620607597162004480000000⟩,
  ⟨1, 5, 8, 7, 2, 5, -11515848714542863036973614525659811183161507840000000⟩
]

def collectedFourData_10_1_14 : List CollectedFourTerm := [
  ⟨1, 6, 3, 0, 4, 6, 2748213688397789966811642217453542273563649638400000⟩,
  ⟨1, 6, 4, 0, 5, 6, -161895907391180532175759870353928557459106116403200000⟩,
  ⟨1, 6, 5, 0, 6, 6, -141204165624479399366522774314055978850812166144000000⟩,
  ⟨1, 6, 6, 0, 7, 6, -64812636366047117790574479616380853173331427328000000⟩,
  ⟨1, 6, 7, 0, 8, 6, -47528742635459416254227061091648614637366149120000000⟩,
  ⟨1, 6, 3, 1, 3, 6, -13191899887852231004541841458216734010457561497600000⟩,
  ⟨1, 6, 4, 1, 4, 6, -49820742708529597029668616474096941390443944345600000⟩,
  ⟨1, 6, 5, 1, 5, 6, 46284298932022751914862438045208700477463592960000000⟩,
  ⟨1, 6, 6, 1, 6, 6, 23883801148071945903019323448809683925942140928000000⟩,
  ⟨1, 6, 7, 1, 7, 6, 3759981082551625875060093085776038109747609600000000⟩,
  ⟨1, 6, 8, 1, 8, 6, 10867414542404151600604630032787983663023888793600000⟩,
  ⟨1, 6, 3, 2, 2, 6, 10295137752692991195210385673343502683944150630400000⟩,
  ⟨1, 6, 4, 2, 3, 6, -78224091059670375518195405317877706219818739302400000⟩,
  ⟨1, 6, 5, 2, 4, 6, -34768739950790639366160705992932817844773584896000000⟩,
  ⟨1, 6, 6, 2, 5, 6, 429097249863323237187122288449961164089065472000000⟩,
  ⟨1, 6, 7, 2, 6, 6, 2358249485004092578404263951454674070842376192000000⟩,
  ⟨1, 6, 8, 2, 7, 6, 4666221564408189907699942344184891054625076019200000⟩,
  ⟨1, 6, 3, 3, 1, 6, 230664623993342548237699579652290723333118361600000⟩,
  ⟨1, 6, 4, 3, 2, 6, 208687553334807293763223270382217650636797142630400000⟩,
  ⟨1, 6, 5, 3, 3, 6, 10382139276818387894823194555677536776909488128000000⟩,
  ⟨1, 6, 6, 3, 4, 6, -6948248387116308071214469601579849057323450368000000⟩,
  ⟨1, 6, 7, 3, 5, 6, 5656229305556154420321826131918554601187442688000000⟩,
  ⟨1, 6, 8, 3, 6, 6, -250571102703781736530418894682432208543678464000000⟩,
  ⟨1, 6, 3, 4, 0, 6, -44228409598139271913157905949206144012728768921600000⟩,
  ⟨1, 6, 4, 4, 1, 6, -2679169510203187961086622654451444518077071360000000⟩,
  ⟨1, 6, 5, 4, 2, 6, 21442075080071952452877468344427991351752130560000000⟩,
  ⟨1, 6, 6, 4, 3, 6, 8772926264169097596753644611214127503668936704000000⟩,
  ⟨1, 6, 7, 4, 4, 6, -2924298177521889227752737959606940782787821568000000⟩,
  ⟨1, 6, 8, 4, 5, 6, -3410556602415684001311201076898597278824844492800000⟩,
  ⟨1, 6, 4, 5, 0, 6, -859929337801880833785693247565278042287995722137600000⟩,
  ⟨1, 6, 5, 5, 1, 6, 7239173204533979398154059495476313370941980672000000⟩,
  ⟨1, 6, 6, 5, 2, 6, -19043711475114268417563532377150334635161419776000000⟩,
  ⟨1, 6, 7, 5, 3, 6, -3335700446813337210475891005681450848171851776000000⟩,
  ⟨1, 6, 8, 5, 4, 6, -1707332478287480880695804430662301173267457638400000⟩,
  ⟨1, 6, 5, 6, 0, 6, -384391570955068536517550710449468888698811580416000000⟩,
  ⟨1, 6, 6, 6, 1, 6, 35665111884941538243773500218584331506556076032000000⟩,
  ⟨1, 6, 7, 6, 2, 6, -23608408400518757780259156262074609178326859776000000⟩,
  ⟨1, 6, 8, 6, 3, 6, 9064912389487727182426808953030033363696405708800000⟩,
  ⟨1, 6, 6, 7, 0, 6, 10583012003759802529066049114819906157699661824000000⟩,
  ⟨1, 6, 7, 7, 1, 6, 122138947737824472778296108750019142155814043648000000⟩,
  ⟨1, 6, 8, 7, 2, 6, -3565471407312962418959075782794609821605901107200000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1004. -/
namespace LaughlinFock
def collectedFourData_10_1_15 : List CollectedFourTerm := [
  ⟨1, 7, 2, 0, 3, 7, 4727508290973887038058176422234107098158858240000000⟩,
  ⟨1, 7, 3, 0, 4, 7, 1730584074975734568199980062829994736898539520000000⟩,
  ⟨1, 7, 4, 0, 5, 7, -50973925411576204575404918300461660474158612480000000⟩,
  ⟨1, 7, 5, 0, 6, 7, -29639335226078607141499087487839807151171174400000000⟩,
  ⟨1, 7, 6, 0, 7, 7, -10203329241263059502989456686536183271496089600000000⟩,
  ⟨1, 7, 7, 0, 8, 7, -5985887156868033279954772664833386990482227200000000⟩,
  ⟨1, 7, 2, 1, 2, 7, -4534688759755647838836990051510777764904960000000000⟩,
  ⟨1, 7, 3, 1, 3, 7, -8307102159112296762007027960600000720042721280000000⟩,
  ⟨1, 7, 4, 1, 4, 7, -15686368257831958959723967958049406414844067840000000⟩,
  ⟨1, 7, 5, 1, 5, 7, 9715264742249435176167033145417087315869696000000000⟩,
  ⟨1, 7, 6, 1, 6, 7, 3759981082551625875060093085776038109747609600000000⟩,
  ⟨1, 7, 7, 1, 7, 7, 473541297836081271600022057168110643838976000000000⟩,
  ⟨1, 7, 8, 1, 8, 7, 1140557508479190263194376080900498669625671680000000⟩,
  ⟨1, 7, 2, 2, 1, 7, -6283877312718583051365237836610413318079774720000000⟩,
  ⟨1, 7, 3, 2, 2, 7, 6482975293991440317904047907186471100083077120000000⟩,
  ⟨1, 7, 4, 2, 3, 7, -24629337747429682109939025256647241233711759360000000⟩,
  ⟨1, 7, 5, 2, 4, 7, -7298101541355536560242161134659328760453529600000000⟩,
  ⟨1, 7, 6, 2, 5, 7, 67551958419787272161519103365371595744870400000000⟩,
  ⟨1, 7, 7, 2, 6, 7, 297003760718994308667427086606949768778219520000000⟩,
  ⟨1, 7, 8, 2, 7, 7, 489729550735983099088049505268131769048104960000000⟩,
  ⟨1, 7, 2, 3, 0, 7, 10882181758326020038686736622115653120038010880000000⟩,
  ⟨1, 7, 3, 3, 1, 7, 145252360334421131702460406594311285091860480000000⟩,
  ⟨1, 7, 4, 3, 2, 7, 65706563862109678945658992849755059715110338560000000⟩,
  ⟨1, 7, 5, 3, 3, 7, 2179253742469695930442551551612258377059532800000000⟩,
  ⟨1, 7, 6, 3, 4, 7, -1093849439226978548634827328541036744645017600000000⟩,
  ⟨1, 7, 7, 3, 5, 7, 712359479317875498727337650696709479889633280000000⟩,
  ⟨1, 7, 8, 3, 6, 7, -26297952606994628125582344144354974839603200000000⟩,
  ⟨1, 7, 3, 4, 0, 7, -27851175341706119190771003120516363989790228480000000⟩,
  ⟨1, 7, 4, 4, 1, 7, -843553051950133146556741596667281150050304000000000⟩,
  ⟨1, 7, 5, 4, 2, 7, 4500779764041341467877271959352809625747456000000000⟩,
  ⟨1, 7, 6, 4, 3, 7, 1381104983557399935144896106336852600736972800000000⟩,
  ⟨1, 7, 7, 4, 4, 7, -368293330163154921711502910076040983431086080000000⟩,
  ⟨1, 7, 8, 4, 5, 7, -357944930305192072251650818776682591829360640000000⟩,
  ⟨1, 7, 4, 5, 0, 7, -270754058151856025484814181690247499395775856640000000⟩,
  ⟨1, 7, 5, 5, 1, 7, 1519532234901936156291565584432147576599347200000000⟩,
  ⟨1, 7, 6, 5, 2, 7, -2998015033037624424051054069133739790906163200000000⟩,
  ⟨1, 7, 7, 5, 3, 7, -420106347371415407379040550207012259558850560000000⟩,
  ⟨1, 7, 8, 5, 4, 7, -179188055262164974029524002563528511633489920000000⟩,
  ⟨1, 7, 5, 6, 0, 7, -80685371987645722941306772822844404569577881600000000⟩,
  ⟨1, 7, 6, 6, 1, 7, 5614690273256305753904011286742062997071462400000000⟩,
  ⟨1, 7, 7, 6, 2, 7, -2973301223696355358075277700955748726011330560000000⟩,
  ⟨1, 7, 8, 6, 3, 7, 951381200118367862543636735818312705313341440000000⟩,
  ⟨1, 7, 6, 7, 0, 7, 1666063315627876672395386597190337452362956800000000⟩,
  ⟨1, 7, 7, 7, 1, 7, 15382480538665999928179418212117328308343930880000000⟩,
  ⟨1, 7, 8, 7, 2, 7, -374203557710150853647948737581424215179919360000000⟩
]

def collectedFourData_10_1_16 : List CollectedFourTerm := [
  ⟨1, 8, 1, 0, 2, 8, -71821454090837103110257157637922310291793641472000000⟩,
  ⟨1, 8, 2, 0, 3, 8, 68319216536856617967971449697165181962838815539200000⟩,
  ⟨1, 8, 3, 0, 4, 8, 12504700243386203280518294734779027073364970700800000⟩,
  ⟨1, 8, 4, 0, 5, 8, -245548566220116427286835539525708288497279618252800000⟩,
  ⟨1, 8, 5, 0, 6, 8, -107082634058257828318312844947588597695998066688000000⟩,
  ⟨1, 8, 6, 0, 7, 8, -29490522995448399860115940807419808464611416473600000⟩,
  ⟨1, 8, 7, 0, 8, 8, -14417430059158799634178135557913115519505924096000000⟩,
  ⟨1, 8, 1, 1, 1, 8, 70993500039696456769917706874495824031300085350400000⟩,
  ⟨1, 8, 2, 1, 2, 8, -65532700153377083929535023243088130061683916800000000⟩,
  ⟨1, 8, 3, 1, 3, 8, -60024718759960921175697507179048210728999924531200000⟩,
  ⟨1, 8, 4, 1, 4, 8, -75563441579420628088525319690586318547894822502400000⟩,
  ⟨1, 8, 5, 1, 5, 8, 35099847254942334260212392345414692312627281920000000⟩,
  ⟨1, 8, 6, 1, 6, 8, 10867414542404151600604630032787983663023888793600000⟩,
  ⟨1, 8, 7, 1, 7, 8, 1140557508479190263194376080900498669625671680000000⟩,
  ⟨1, 8, 8, 1, 8, 8, 2354668240147381908219921481635234153820795699200000⟩,
  ⟨1, 8, 1, 2, 0, 8, 134771161807576179966215825446176160802909297049600000⟩,
  ⟨1, 8, 2, 2, 1, 8, -90810961799544919660363233829137711803083102617600000⟩,
  ⟨1, 8, 3, 2, 2, 8, 46844105356613892886444802547149373273952537804800000⟩,
  ⟨1, 8, 4, 2, 3, 8, -118642983093841052617968289278011878086666721689600000⟩,
  ⟨1, 8, 5, 2, 4, 8, -26366985990474174429153501939112861135527739392000000⟩,
  ⟨1, 8, 6, 2, 5, 8, 195244369368179424273672690929222845209142886400000⟩,
  ⟨1, 8, 7, 2, 6, 8, 715354438741825928733248184402761418815412633600000⟩,
  ⟨1, 8, 8, 2, 7, 8, 1011041188898284128335275050214839232886105702400000⟩,
  ⟨1, 8, 2, 3, 0, 8, 157262999064428940425194896602146023765967267430400000⟩,
  ⟨1, 8, 3, 3, 1, 8, 1049551565792447412223304604431026775297045299200000⟩,
  ⟨1, 8, 4, 3, 2, 8, 316517757212542889176984914983123108633647880601600000⟩,
  ⟨1, 8, 5, 3, 3, 8, 7873328778968222191405242296040792180765229056000000⟩,
  ⟨1, 8, 6, 3, 4, 8, -3161535933842740513501420543991086562726746521600000⟩,
  ⟨1, 8, 7, 3, 5, 8, 1715767888851746644568567001916766341290157670400000⟩,
  ⟨1, 8, 8, 3, 6, 8, -54291829499381261421061730769849716790263808000000⟩,
  ⟨1, 8, 3, 4, 0, 8, -201244541718614634579298077786565757258567988019200000⟩,
  ⟨1, 8, 4, 4, 1, 8, -4063513664378661255592545710771653427268157440000000⟩,
  ⟨1, 8, 5, 4, 2, 8, 16260666738085118870831437692894931911306117120000000⟩,
  ⟨1, 8, 6, 4, 3, 8, 3991786142900748300222664839422436616306478284800000⟩,
  ⟨1, 8, 7, 4, 4, 8, -887060378809447783469288308128194007394575974400000⟩,
  ⟨1, 8, 8, 4, 5, 8, -738973311600255645169473813327433931834366361600000⟩,
  ⟨1, 8, 4, 5, 0, 8, -1304260369211586918445714888322540280058625812070400000⟩,
  ⟨1, 8, 5, 5, 1, 8, 5489850329253101917696678852279817966708588544000000⟩,
  ⟨1, 8, 6, 5, 2, 8, -8665115981453079153428423053658599300793578291200000⟩,
  ⟨1, 8, 7, 5, 3, 8, -1011855673504735956450369414604174050565344460800000⟩,
  ⟨1, 8, 8, 5, 4, 8, -369931739173932234589077586382957018815974604800000⟩,
  ⟨1, 8, 5, 6, 0, 8, -291504586607780609949558616226531491685892882432000000⟩,
  ⟨1, 8, 6, 6, 1, 8, 16228051521278612588260070292126149405183469158400000⟩,
  ⟨1, 8, 7, 6, 2, 8, -7161405037224717450276270931643486824825670860800000⟩,
  ⟨1, 8, 8, 6, 3, 8, 1964115863985734444421032753168142217661487513600000⟩,
  ⟨1, 8, 6, 7, 0, 8, 4815396755276591446690921112689123292525415628800000⟩,
  ⟨1, 8, 7, 7, 1, 8, 37049785853067622424865172716190256854527796838400000⟩,
  ⟨1, 8, 8, 7, 2, 8, -772539066324796817322429683032946405601076838400000⟩
]

def collectedFourData_10_1_17 : List CollectedFourTerm := [
  ⟨2, 0, 8, 1, 8, 1, 134771161807576179966215825446176160802909297049600000⟩,
  ⟨2, 0, 8, 2, 7, 1, 57867683158034269165026248429261880815739155251200000⟩,
  ⟨2, 0, 8, 3, 6, 1, -3107432636808517153215063811966461713426939904000000⟩,
  ⟨2, 0, 8, 4, 5, 1, -42295678877855356563070309818695611558837144780800000⟩,
  ⟨2, 0, 8, 5, 4, 1, -21173314111905431537176821456952826898963392102400000⟩,
  ⟨2, 0, 8, 6, 3, 1, 112417610430537927083171212384029616324263857356800000⟩,
  ⟨2, 0, 8, 7, 2, 1, -44216839440538874404104891381816422272523776819200000⟩
]

def collectedFourData_10_1_18 : List CollectedFourTerm := [
  ⟨2, 1, 7, 0, 8, 2, 79432523991935027999686078820741145760559529984000000⟩,
  ⟨2, 1, 7, 1, 7, 2, -6283877312718583051365237836610413318079774720000000⟩,
  ⟨2, 1, 8, 1, 8, 2, -90810961799544919660363233829137711803083102617600000⟩,
  ⟨2, 1, 7, 2, 6, 2, -3941230051745620781633912200764249790547912294400000⟩,
  ⟨2, 1, 8, 2, 7, 2, -38992169349964060657538036240180121308555850547200000⟩,
  ⟨2, 1, 7, 3, 5, 2, -9452986658272711165767452442558167622721575321600000⟩,
  ⟨2, 1, 8, 3, 6, 2, 2093837752016871772534976482508911039400116224000000⟩,
  ⟨2, 1, 7, 4, 4, 2, 4887240273263207609082956704930393410783254937600000⟩,
  ⟨2, 1, 8, 4, 5, 2, 28499504102715424887250447792015982639065124044800000⟩,
  ⟨2, 1, 7, 5, 3, 2, 5574797292738178666861973212355117237071459123200000⟩,
  ⟨2, 1, 8, 5, 4, 2, 14266917292968834350310907211040083302116910694400000⟩,
  ⟨2, 1, 7, 6, 2, 2, 39455608600226967464297135810949244857387004723200000⟩,
  ⟨2, 1, 8, 6, 3, 2, -75748781783001708919419077846373571923112938700800000⟩,
  ⟨2, 1, 7, 7, 1, 2, -204125006439709334470244536375948630132705040793600000⟩,
  ⟨2, 1, 8, 7, 2, 2, 29794012780452724997399689018526149912523125555200000⟩
]

def collectedFourData_10_1_19 : List CollectedFourTerm := [
  ⟨2, 2, 6, 0, 7, 3, -27937555473975275414139855678259908537976514150400000⟩,
  ⟨2, 2, 7, 0, 8, 3, -81949259183787478742599978229047951631019147264000000⟩,
  ⟨2, 2, 6, 1, 6, 3, 10295137752692991195210385673343502683944150630400000⟩,
  ⟨2, 2, 7, 1, 7, 3, 6482975293991440317904047907186471100083077120000000⟩,
  ⟨2, 2, 8, 1, 8, 3, 46844105356613892886444802547149373273952537804800000⟩,
  ⟨2, 2, 6, 2, 5, 3, 184962823516107478773646199152168980258068889600000⟩,
  ⟨2, 2, 7, 2, 6, 3, 4066103741664145366093206450415524735365834342400000⟩,
  ⟨2, 2, 8, 2, 7, 3, 20113797419573205108453822012397798899859429785600000⟩,
  ⟨2, 2, 6, 3, 4, 3, -2995049818151073773521856816990209490385528422400000⟩,
  ⟨2, 2, 7, 3, 5, 3, 9752494504622931024828637270116192844905027993600000⟩,
  ⟨2, 2, 8, 3, 6, 3, -1080089389116297877923596133230083224373297152000000⟩,
  ⟨2, 2, 6, 4, 3, 3, 3781579147468754210664824241752256124401431347200000⟩,
  ⟨2, 2, 7, 4, 4, 3, -5042087292703367152208854990739233000400722329600000⟩,
  ⟨2, 2, 8, 4, 5, 3, -14701240316623774569216122203159704551712777830400000⟩,
  ⟨2, 2, 6, 5, 2, 3, -8208811978602018767962672967922805508519283916800000⟩,
  ⟨2, 2, 7, 5, 3, 3, -5751428826384301651285262307940938704305206067200000⟩,
  ⟨2, 2, 8, 5, 4, 3, -7359474710345793360145407138607970613808280371200000⟩,
  ⟨2, 2, 6, 6, 1, 3, 15373484209833242076482404060134409466206067097600000⟩,
  ⟨2, 2, 7, 6, 2, 3, -40705717670036073833790582586501631340631503667200000⟩,
  ⟨2, 2, 8, 6, 3, 3, 39074400756934491716949588067285267891500770918400000⟩,
  ⟨2, 2, 6, 7, 0, 3, 4561818520495682320759413641331303289216774963200000⟩,
  ⟨2, 2, 7, 7, 1, 3, 210592490556115917415671054642237028767561783705600000⟩,
  ⟨2, 2, 8, 7, 2, 3, -15369002222051373652680999046829024800826562969600000⟩
]

def collectedFourData_10_1_20 : List CollectedFourTerm := [
  ⟨2, 3, 5, 0, 6, 4, 154157029435069959229951926148407651263125546598400000⟩,
  ⟨2, 3, 6, 0, 7, 4, 212273981745332405885081892997584833441266296422400000⟩,
  ⟨2, 3, 7, 0, 8, 4, 311331740606787571068149300901760466479472443392000000⟩,
  ⟨2, 3, 5, 1, 5, 4, -50530025097279876427275652912549489889935097856000000⟩,
  ⟨2, 3, 6, 1, 6, 4, -78224091059670375518195405317877706219818739302400000⟩,
  ⟨2, 3, 7, 1, 7, 4, -24629337747429682109939025256647241233711759360000000⟩,
  ⟨2, 3, 8, 1, 8, 4, -118642983093841052617968289278011878086666721689600000⟩,
  ⟨2, 3, 5, 2, 4, 4, 37958127115515728706654494819941578913009473945600000⟩,
  ⟨2, 3, 6, 2, 5, 4, -1405376897030160175547703731959009669700753817600000⟩,
  ⟨2, 3, 7, 2, 6, 4, -15447450873729340694482017157602619459735073587200000⟩,
  ⟨2, 3, 8, 2, 7, 4, -50942608659862870150912498305022260775528641331200000⟩,
  ⟨2, 3, 5, 3, 3, 4, -11334508036765922530726754499736317684519587020800000⟩,
  ⟨2, 3, 6, 3, 4, 4, 22756864000388412439534222054324235685513815654400000⟩,
  ⟨2, 3, 7, 3, 5, 4, -37050500756486028653293188527335021706960751820800000⟩,
  ⟨2, 3, 8, 3, 6, 4, 2735563549719267187321596962055508361692053504000000⟩,
  ⟨2, 3, 5, 4, 2, 4, -23408987862710716408212999157908318137106825216000000⟩,
  ⟨2, 3, 6, 4, 3, 4, -28733038710780598982577465877031075574713627443200000⟩,
  ⟨2, 3, 7, 4, 4, 4, 19155289855741124805518029038359588704111873228800000⟩,
  ⟨2, 3, 8, 4, 5, 4, 37234119278519351487279342605257363473711287500800000⟩,
  ⟨2, 3, 5, 5, 1, 4, -7903233108184224736354591095638699293036196659200000⟩,
  ⟨2, 3, 6, 5, 2, 4, 62371856611429060434549305544657041306399067340800000⟩,
  ⟨2, 3, 7, 5, 3, 4, 21850134648301053122579227514841531239536105881600000⟩,
  ⟨2, 3, 8, 5, 4, 4, 18639485736615251147346802218009371338795804262400000⟩,
  ⟨2, 3, 5, 6, 0, 4, 419652369717628537378340401767131265903149816217600000⟩,
  ⟨2, 3, 6, 6, 1, 4, -116810173658903342955771799707699726071570733465600000⟩,
  ⟨2, 3, 7, 6, 2, 4, 154644252566568332262602744312529618368160438681600000⟩,
  ⟨2, 3, 8, 6, 3, 4, -98964500082023838400228873920899608068664118476800000⟩,
  ⟨2, 3, 6, 7, 0, 4, -34661421334707458446796101295195538295409029939200000⟩,
  ⟨2, 3, 7, 7, 1, 4, -800057588031558346210904483283752782226728471756800000⟩,
  ⟨2, 3, 8, 7, 2, 4, 38925372934731444251003138018887307198159074099200000⟩
]

def collectedFourData_10_1_21 : List CollectedFourTerm := [
  ⟨2, 4, 4, 0, 5, 5, 78559755044625612243191090080679173082212781260800000⟩,
  ⟨2, 4, 5, 0, 6, 5, 137038234523575709722952627699937844348921577472000000⟩,
  ⟨2, 4, 6, 0, 7, 5, 94350714334186371794015708391828220245700509696000000⟩,
  ⟨2, 4, 7, 0, 8, 5, 92253014648451846318304778107381982973520773120000000⟩,
  ⟨2, 4, 4, 1, 4, 5, 24175443384534977094453537663814864399222859366400000⟩,
  ⟨2, 4, 5, 1, 5, 5, -44918778307672205949044392780983309724790292480000000⟩,
  ⟨2, 4, 6, 1, 6, 5, -34768739950790639366160705992932817844773584896000000⟩,
  ⟨2, 4, 7, 1, 7, 5, -7298101541355536560242161134659328760453529600000000⟩,
  ⟨2, 4, 8, 1, 8, 5, -26366985990474174429153501939112861135527739392000000⟩,
  ⟨2, 4, 4, 2, 3, 5, 37958127115515728706654494819941578913009473945600000⟩,
  ⟨2, 4, 5, 2, 4, 5, 33742961607356832717842959939052224580627202048000000⟩,
  ⟨2, 4, 6, 2, 5, 5, -624656460736849306021524791194136612022779904000000⟩,
  ⟨2, 4, 7, 2, 6, 5, -4577348615203560328055197333407451702301294592000000⟩,
  ⟨2, 4, 8, 2, 7, 5, -11321386346046287821029435066272997933343309824000000⟩,
  ⟨2, 4, 4, 3, 2, 5, -101265333602483704024560573557656706543263521177600000⟩,
  ⟨2, 4, 5, 3, 3, 5, -10075836153847960835049082025667662874478116864000000⟩,
  ⟨2, 4, 6, 3, 4, 5, 10114882458927583434443058359078121912429182976000000⟩,
  ⟨2, 4, 7, 3, 5, 5, -10978708378268267875298638332221887695487500288000000⟩,
  ⟨2, 4, 8, 3, 6, 5, 607946326960182696928696201315320781162414080000000⟩,
  ⟨2, 4, 4, 4, 1, 5, 1300063132145969806655313232481225914806435840000000⟩,
  ⟨2, 4, 5, 4, 2, 5, -20809471877121557541141848129403264271940321280000000⟩,
  ⟨2, 4, 6, 4, 3, 5, -12771149365852932705670245270843033052017328128000000⟩,
  ⟨2, 4, 7, 4, 4, 5, 5676045854537262931915405461642545819358855168000000⟩,
  ⟨2, 4, 8, 4, 5, 5, 8274838307191286473912985178095616075094818816000000⟩,
  ⟨2, 4, 4, 5, 0, 5, 417279468159570368916193915982570655344161613414400000⟩,
  ⟨2, 4, 5, 5, 1, 5, -7025596666871492008520577424158650769170497536000000⟩,
  ⟨2, 4, 6, 5, 2, 5, 27722800398109438371460759374878896498233311232000000⟩,
  ⟨2, 4, 7, 5, 3, 5, 6474575280540527209815993262530831086021246976000000⟩,
  ⟨2, 4, 8, 5, 4, 5, 4142403085888779942287659142861031022314651648000000⟩,
  ⟨2, 4, 5, 6, 0, 5, 373050908352907068897657739953608563305436151808000000⟩,
  ⟨2, 4, 6, 6, 1, 5, -51919331967118148038893856299746508596601421824000000⟩,
  ⟨2, 4, 7, 6, 2, 5, 45823784203683224438921801606917583311497854976000000⟩,
  ⟨2, 4, 8, 6, 3, 5, -21993678169345193579004426170157513093295374336000000⟩,
  ⟨2, 4, 6, 7, 0, 5, -15406173831945685868124594568372089587622739968000000⟩,
  ⟨2, 4, 7, 7, 1, 5, -237070991362553248362159280259827281839152693248000000⟩,
  ⟨2, 4, 8, 7, 2, 5, 8650699232943728914576337451619603301410013184000000⟩
]

def collectedFourData_10_1_22 : List CollectedFourTerm := [
  ⟨2, 5, 3, 0, 4, 6, 49374508204002039818412679586577934515280281600000⟩,
  ⟨2, 5, 4, 0, 5, 6, -2908627826659443774219239867363299503056407756800000⟩,
  ⟨2, 5, 5, 0, 6, 6, -2536879233044550577971803936855234042507821056000000⟩,
  ⟨2, 5, 6, 0, 7, 6, -1164426208736355477857756215553629625172099072000000⟩,
  ⟨2, 5, 7, 0, 8, 6, -853903138277622310613399354709638340547706880000000⟩,
  ⟨2, 5, 3, 1, 3, 6, -237006158578180728717327622369795712013985382400000⟩,
  ⟨2, 5, 4, 1, 4, 6, -895081295889286406756655532357708606293304934400000⟩,
  ⟨2, 5, 5, 1, 5, 6, 831545416931516204025489389706185840567255040000000⟩,
  ⟨2, 5, 6, 1, 6, 6, 429097249863323237187122288449961164089065472000000⟩,
  ⟨2, 5, 7, 1, 7, 6, 67551958419787272161519103365371595744870400000000⟩,
  ⟨2, 5, 8, 1, 8, 6, 195244369368179424273672690929222845209142886400000⟩,
  ⟨2, 5, 3, 2, 2, 6, 184962823516107478773646199152168980258068889600000⟩,
  ⟨2, 5, 4, 2, 3, 6, -1405376897030160175547703731959009669700753817600000⟩,
  ⟨2, 5, 5, 2, 4, 6, -624656460736849306021524791194136612022779904000000⟩,
  ⟨2, 5, 6, 2, 5, 6, 7709176973077041555512809863153608848048128000000⟩,
  ⟨2, 5, 7, 2, 6, 6, 42368396983096763892164088238697348918673408000000⟩,
  ⟨2, 5, 8, 2, 7, 6, 83833508248000283151020373522182424840948940800000⟩,
  ⟨2, 5, 3, 3, 1, 6, 4144129118420956070433452711655722386351718400000⟩,
  ⟨2, 5, 4, 3, 2, 6, 3749288258661466472327995406039553208294676889600000⟩,
  ⟨2, 5, 5, 3, 3, 6, 186525896098427105931566418917373085873078272000000⟩,
  ⟨2, 5, 6, 3, 4, 6, -124832486076847232206872811040095971450028032000000⟩,
  ⟨2, 5, 7, 3, 5, 6, 101620023737570322813845284561841103896051712000000⟩,
  ⟨2, 5, 8, 3, 6, 6, -4501769647085372588824601674405708862324736000000⟩,
  ⟨2, 5, 3, 4, 0, 6, -794609233544142969677005163853208864296429158400000⟩,
  ⟨2, 5, 4, 4, 1, 6, -48134057959139378754468735044803371875696640000000⟩,
  ⟨2, 5, 5, 4, 2, 6, 385229109519885353450600087876663822977597440000000⟩,
  ⟨2, 5, 6, 4, 3, 6, 157614715926931415201187870079458240412778496000000⟩,
  ⟨2, 5, 7, 4, 4, 6, -52538048611925705716387905360921448868216832000000⟩,
  ⟨2, 5, 8, 4, 5, 6, -61274185357966333183189755144736136397796147200000⟩,
  ⟨2, 5, 4, 5, 0, 6, -15449522110820423861581441277531495156324656742400000⟩,
  ⟨2, 5, 5, 5, 1, 6, 130059252046676523515854533390060313984892928000000⟩,
  ⟨2, 5, 6, 5, 2, 6, -342140020782320390663095924406777867900289024000000⟩,
  ⟨2, 5, 7, 5, 3, 6, -59929316913233825284874018353043080451457024000000⟩,
  ⟨2, 5, 8, 5, 4, 6, -30673998099947805287430510702343977761872281600000⟩,
  ⟨2, 5, 5, 6, 0, 6, -6905993101553582282428310402070145471698960384000000⟩,
  ⟨2, 5, 6, 6, 1, 6, 640760711874020930252682953886748450454765568000000⟩,
  ⟨2, 5, 7, 6, 2, 6, -424149533631942834511062195479048479806849024000000⟩,
  ⟨2, 5, 8, 6, 3, 6, 162860549393543820877390256664445232811815731200000⟩,
  ⟨2, 5, 6, 7, 0, 6, 190134782898678556927606106660504244244709376000000⟩,
  ⟨2, 5, 7, 7, 1, 6, 2194352827281493139568817399649202707210698752000000⟩,
  ⟨2, 5, 8, 7, 2, 6, -64057390440458054456540817225009332740738252800000⟩
]

def collectedFourData_10_1_23 : List CollectedFourTerm := [
  ⟨2, 6, 2, 0, 3, 7, 2965079809650524249543286340392774066089282764800000⟩,
  ⟨2, 6, 3, 0, 4, 7, 1085417430025533741321892308754157746950399590400000⟩,
  ⟨2, 6, 4, 0, 5, 7, -31970701636857529805466873684572480474321623449600000⟩,
  ⟨2, 6, 5, 0, 6, 7, -18589707101752107091347780705731467175408959488000000⟩,
  ⟨2, 6, 6, 0, 7, 7, -6399499199662643249808074256751586264368545792000000⟩,
  ⟨2, 6, 7, 0, 8, 7, -3754331470039472136232038906915330035804012544000000⟩,
  ⟨2, 6, 2, 1, 2, 7, -2844143945822837099624412615096181571400499200000000⟩,
  ⟨2, 6, 3, 1, 3, 7, -5210190944713078538824710410984595073904777625600000⟩,
  ⟨2, 6, 4, 1, 4, 7, -9838445740400568559164843359793989168814410956800000⟩,
  ⟨2, 6, 5, 1, 5, 7, 6093386528301388685726103080273871393175633920000000⟩,
  ⟨2, 6, 6, 1, 6, 7, 2358249485004092578404263951454674070842376192000000⟩,
  ⟨2, 6, 7, 1, 7, 7, 297003760718994308667427086606949768778219520000000⟩,
  ⟨2, 6, 8, 1, 8, 7, 715354438741825928733248184402761418815412633600000⟩,
  ⟨2, 6, 2, 2, 1, 7, -3941230051745620781633912200764249790547912294400000⟩,
  ⟨2, 6, 3, 2, 2, 7, 4066103741664145366093206450415524735365834342400000⟩,
  ⟨2, 6, 4, 2, 3, 7, -15447450873729340694482017157602619459735073587200000⟩,
  ⟨2, 6, 5, 2, 4, 7, -4577348615203560328055197333407451702301294592000000⟩,
  ⟨2, 6, 6, 2, 5, 7, 42368396983096763892164088238697348918673408000000⟩,
  ⟨2, 6, 7, 2, 6, 7, 186279917473555588178760595080963818007193190400000⟩,
  ⟨2, 6, 8, 2, 7, 7, 307156987085336092974150356081459492405064499200000⟩,
  ⟨2, 6, 2, 3, 0, 7, 6825273575546215977411363251652357218891307417600000⟩,
  ⟨2, 6, 3, 3, 1, 7, 91101868981165094619263911107977550065408409600000⟩,
  ⟨2, 6, 4, 3, 2, 7, 41210970743515999651225961896658247058856293171200000⟩,
  ⟨2, 6, 5, 3, 3, 7, 1366821774641691552369537544088183161441222656000000⟩,
  ⟨2, 6, 6, 3, 4, 7, -686059270005281792494102055336569183615844352000000⟩,
  ⟨2, 6, 7, 3, 5, 7, 446789847702936552296699327925679301166995865600000⟩,
  ⟨2, 6, 8, 3, 6, 7, -16494001387374160639269982567849736288600064000000⟩,
  ⟨2, 6, 3, 4, 0, 7, -17468178287153743341191701330421848506577295769600000⟩,
  ⟨2, 6, 4, 4, 1, 7, -529074084858169797174692698638968820942766080000000⟩,
  ⟨2, 6, 5, 4, 2, 7, 2822876319756484138960170103237082229107589120000000⟩,
  ⟨2, 6, 6, 4, 3, 7, 866225133771295913134218178668526290868371456000000⟩,
  ⟨2, 6, 7, 4, 4, 7, -230992533504529178108253965673985437022656921600000⟩,
  ⟨2, 6, 8, 4, 5, 7, -224502046424978230008355363675187193108548812800000⟩,
  ⟨2, 6, 4, 5, 0, 7, -169816178374513323710857772682077639923437718732800000⟩,
  ⟨2, 6, 5, 5, 1, 7, 953046313725810326857599472764998029299154944000000⟩,
  ⟨2, 6, 6, 5, 2, 7, -1880346536982458570610043281198790363016331264000000⟩,
  ⟨2, 6, 7, 5, 3, 7, -263489511139578434236895435303524669714543411200000⟩,
  ⟨2, 6, 8, 5, 4, 7, -112386240718561751735521220016935779244074598400000⟩,
  ⟨2, 6, 5, 6, 0, 7, -50605636773071877129143232526427128979502661632000000⟩,
  ⟨2, 6, 6, 6, 1, 7, 3521517836036178896780536617808495623429685248000000⟩,
  ⟨2, 6, 7, 6, 2, 7, -1864846105764335045925858010258787367094793011200000⟩,
  ⟨2, 6, 8, 6, 3, 7, 596703593971050573190656818820502607331380428800000⟩,
  ⟨2, 6, 6, 7, 0, 7, 1044950192514620089443715760728165014501851136000000⟩,
  ⟨2, 6, 7, 7, 1, 7, 9647848223687570193593086904576654285102225817600000⟩,
  ⟨2, 6, 8, 7, 2, 7, -234699411481559209358826456793273709674836787200000⟩
]

def collectedFourData_10_1_24 : List CollectedFourTerm := [
  ⟨2, 7, 1, 0, 2, 8, -30838505014981829971544030689925013690944323584000000⟩,
  ⟨2, 7, 2, 0, 3, 8, 29334723565006092389153157449310880485450606182400000⟩,
  ⟨2, 7, 3, 0, 4, 8, 5369234945853145653235577657752586019854195097600000⟩,
  ⟨2, 7, 4, 0, 5, 8, -105432990554931274129765703201553693900770220441600000⟩,
  ⟨2, 7, 5, 0, 6, 8, -45978856724990028704092526820823344601613991936000000⟩,
  ⟨2, 7, 6, 0, 7, 8, -12662562361092577919451118282809301780491612979200000⟩,
  ⟨2, 7, 7, 0, 8, 8, -6190517789018720247275571452075714660335091712000000⟩,
  ⟨2, 7, 1, 1, 1, 8, 30483000305678919914152270691593694684474297548800000⟩,
  ⟨2, 7, 2, 1, 2, 8, -28138256568423441102594602132985011638999449600000000⟩,
  ⟨2, 7, 3, 1, 3, 8, -25773254161086199289635459104110073140820207206400000⟩,
  ⟨2, 7, 4, 1, 4, 8, -32445229654484840959336414674891306841756454092800000⟩,
  ⟨2, 7, 5, 1, 5, 8, 15071079098838937837597517547918590818375434240000000⟩,
  ⟨2, 7, 6, 1, 6, 8, 4666221564408189907699942344184891054625076019200000⟩,
  ⟨2, 7, 7, 1, 7, 8, 489729550735983099088049505268131769048104960000000⟩,
  ⟨2, 7, 8, 1, 8, 8, 1011041188898284128335275050214839232886105702400000⟩,
  ⟨2, 7, 1, 2, 0, 8, 57867683158034269165026248429261880815739155251200000⟩,
  ⟨2, 7, 2, 2, 1, 8, -38992169349964060657538036240180121308555850547200000⟩,
  ⟨2, 7, 3, 2, 2, 8, 20113797419573205108453822012397798899859429785600000⟩,
  ⟨2, 7, 4, 2, 3, 8, -50942608659862870150912498305022260775528641331200000⟩,
  ⟨2, 7, 5, 2, 4, 8, -11321386346046287821029435066272997933343309824000000⟩,
  ⟨2, 7, 6, 2, 5, 8, 83833508248000283151020373522182424840948940800000⟩,
  ⟨2, 7, 7, 2, 6, 8, 307156987085336092974150356081459492405064499200000⟩,
  ⟨2, 7, 8, 2, 7, 8, 434118177762857447774702757415866239531404492800000⟩,
  ⟨2, 7, 2, 3, 0, 8, 67525168443201999584035356271011484798391471308800000⟩,
  ⟨2, 7, 3, 3, 1, 8, 450653661011044812833788381468962648303756902400000⟩,
  ⟨2, 7, 4, 3, 2, 8, 135905553106520767893923591077702853867607372595200000⟩,
  ⟨2, 7, 5, 3, 3, 8, 3380628979298104223806197189709613689661816832000000⟩,
  ⟨2, 7, 6, 3, 4, 8, -1357491894100946288184151666114881244884054835200000⟩,
  ⟨2, 7, 7, 3, 5, 8, 736711854621859997958802443628228422274960588800000⟩,
  ⟨2, 7, 8, 3, 6, 8, -23311681411680162832365545439324422931480576000000⟩,
  ⟨2, 7, 3, 4, 0, 8, -86409846299937027036344708264337497320495408742400000⟩,
  ⟨2, 7, 4, 4, 1, 8, -1744780694065281858803218886898418850652487680000000⟩,
  ⟨2, 7, 5, 4, 2, 8, 6981961853837782011329338579619777495055728640000000⟩,
  ⟨2, 7, 6, 4, 3, 8, 1713982521585910739058343019232407505941928345600000⟩,
  ⟨2, 7, 7, 4, 4, 8, -380883627138883487044827166406792176590441676800000⟩,
  ⟨2, 7, 8, 4, 5, 8, -317298395920803094793426353837198223579755315200000⟩,
  ⟨2, 7, 4, 5, 0, 8, -560019849861338027031991194024083345761557597388800000⟩,
  ⟨2, 7, 5, 5, 1, 8, 2357217339209655090823142411614792213875130368000000⟩,
  ⟨2, 7, 6, 5, 2, 8, -3720604463277380207215336041932444828483085926400000⟩,
  ⟨2, 7, 7, 5, 3, 8, -434467898997809368124235159204438671776913817600000⟩,
  ⟨2, 7, 8, 5, 4, 8, -158840306676159273910142792506070425000319385600000⟩,
  ⟨2, 7, 5, 6, 0, 8, -125165464411575117021691620194868513057175240704000000⟩,
  ⟨2, 7, 6, 6, 1, 8, 6967957618755322395374989004999595894206418124800000⟩,
  ⟨2, 7, 7, 6, 2, 8, -3074945055769150632201262832230625914333534617600000⟩,
  ⟨2, 7, 8, 6, 3, 8, 843346847933797844417408445359330308620759859200000⟩,
  ⟨2, 7, 6, 7, 0, 8, 2067622256699336399120431400998008765225212313600000⟩,
  ⟨2, 7, 7, 7, 1, 8, 15908338550048866212544591135339097288002555084800000⟩,
  ⟨2, 7, 8, 7, 2, 8, -331710770447434575121785474272560774302715084800000⟩
]

def collectedFourData_10_1_25 : List CollectedFourTerm := [
  ⟨3, 0, 7, 0, 8, 2, -137558249562460946508878114441955578221833486336000000⟩,
  ⟨3, 0, 7, 1, 7, 2, 10882181758326020038686736622115653120038010880000000⟩,
  ⟨3, 0, 8, 1, 8, 2, 157262999064428940425194896602146023765967267430400000⟩,
  ⟨3, 0, 7, 2, 6, 2, 6825273575546215977411363251652357218891307417600000⟩,
  ⟨3, 0, 8, 2, 7, 2, 67525168443201999584035356271011484798391471308800000⟩,
  ⟨3, 0, 7, 3, 5, 2, 16370325812400441347005556290938220454888236646400000⟩,
  ⟨3, 0, 8, 3, 6, 2, -3626029258046526228492163545442938123290935296000000⟩,
  ⟨3, 0, 7, 4, 4, 2, -8463538402097210772017713097792430902639748710400000⟩,
  ⟨3, 0, 8, 4, 5, 2, -49354366457822108598786749514358312368990270259200000⟩,
  ⟨3, 0, 7, 5, 3, 2, -9654223719901826092257994134232885987065515212800000⟩,
  ⟨3, 0, 8, 5, 4, 2, -24706909347013286412312784500615443618303941017600000⟩,
  ⟨3, 0, 7, 6, 2, 2, -68327735060009711833404939140836959671133457612800000⟩,
  ⟨3, 0, 8, 6, 3, 2, 131178883722950797406143223870292500816113906483200000⟩,
  ⟨3, 0, 7, 7, 1, 2, 353495988376542330385624443625347028884918789734400000⟩,
  ⟨3, 0, 8, 7, 2, 2, -51596147768599023666800422442542386287246888140800000⟩
]

def collectedFourData_10_1_26 : List CollectedFourTerm := [
  ⟨3, 1, 6, 0, 7, 3, -625946527720038255238678570641545376795564441600000⟩,
  ⟨3, 1, 7, 0, 8, 3, -1836089570653558219044698773800901702588563456000000⟩,
  ⟨3, 1, 6, 1, 6, 3, 230664623993342548237699579652290723333118361600000⟩,
  ⟨3, 1, 7, 1, 7, 3, 145252360334421131702460406594311285091860480000000⟩,
  ⟨3, 1, 8, 1, 8, 3, 1049551565792447412223304604431026775297045299200000⟩,
  ⟨3, 1, 6, 2, 5, 3, 4144129118420956070433452711655722386351718400000⟩,
  ⟨3, 1, 7, 2, 6, 3, 91101868981165094619263911107977550065408409600000⟩,
  ⟨3, 1, 8, 2, 7, 3, 450653661011044812833788381468962648303756902400000⟩,
  ⟨3, 1, 6, 3, 4, 3, -67104691237806319280665176558771064180152729600000⟩,
  ⟨3, 1, 7, 3, 5, 3, 218506593301051416532844067825116128534226534400000⟩,
  ⟨3, 1, 8, 3, 6, 3, -24199619160466360729330646044995762738167808000000⟩,
  ⟨3, 1, 6, 4, 3, 3, 84727038443344373169523237951443333335010508800000⟩,
  ⟨3, 1, 7, 4, 4, 3, -112968975981774330034085645290492607540389478400000⟩,
  ⟨3, 1, 8, 4, 5, 3, -329384234706598488039570816272655446380747161600000⟩,
  ⟨3, 1, 6, 5, 2, 3, -183920077026748455786739412566700114792624947200000⟩,
  ⟨3, 1, 7, 5, 3, 3, -128861915161395713912885738451583990422621388800000⟩,
  ⟨3, 1, 8, 5, 4, 3, -164890505365639940893086226942713177932877004800000⟩,
  ⟨3, 1, 6, 6, 1, 3, 344445993818896073357305289089070013266421350400000⟩,
  ⟨3, 1, 7, 6, 2, 3, -912019759840704365743969851790335738200771788800000⟩,
  ⟨3, 1, 8, 6, 3, 3, 875469777566195419161112793827199748872444313600000⟩,
  ⟨3, 1, 6, 7, 0, 3, 102208457917987186926535115452520780857658572800000⟩,
  ⟨3, 1, 7, 7, 1, 3, 4718366943389514046026345339136188036418004582400000⟩,
  ⟨3, 1, 8, 7, 2, 3, -344345573984671222344818863751581775176296038400000⟩
]

def collectedFourData_10_1_27 : List CollectedFourTerm := [
  ⟨3, 2, 5, 0, 6, 4, -411262730782341956940361388539909446245198227046400000⟩,
  ⟨3, 2, 6, 0, 7, 4, -566308119237577950076145780494483468484839106150400000⟩,
  ⟨3, 2, 7, 0, 8, 4, -830576083947547362443568507087137362138084933632000000⟩,
  ⟨3, 2, 5, 1, 5, 4, 134804855699171869739117033209050426202103218176000000⟩,
  ⟨3, 2, 6, 1, 6, 4, 208687553334807293763223270382217650636797142630400000⟩,
  ⟨3, 2, 7, 1, 7, 4, 65706563862109678945658992849755059715110338560000000⟩,
  ⟨3, 2, 8, 1, 8, 4, 316517757212542889176984914983123108633647880601600000⟩,
  ⟨3, 2, 5, 2, 4, 4, -101265333602483704024560573557656706543263521177600000⟩,
  ⟨3, 2, 6, 2, 5, 4, 3749288258661466472327995406039553208294676889600000⟩,
  ⟨3, 2, 7, 2, 6, 4, 41210970743515999651225961896658247058856293171200000⟩,
  ⟨3, 2, 8, 2, 7, 4, 135905553106520767893923591077702853867607372595200000⟩,
  ⟨3, 2, 5, 3, 3, 4, 30238392270254110678249708638072743630876757196800000⟩,
  ⟨3, 2, 6, 3, 4, 4, -60711146725774748456989830062813936403970680422400000⟩,
  ⟨3, 2, 7, 3, 5, 4, 98843952648838582437935406281740011055807777996800000⟩,
  ⟨3, 2, 8, 3, 6, 4, -7297982711583327524364407166983386651252752384000000⟩,
  ⟨3, 2, 5, 4, 2, 4, 62450893796731123994260906225490963436442484736000000⟩,
  ⟨3, 2, 6, 4, 3, 4, 76654486708616490626156365124174217221355287347200000⟩,
  ⟨3, 2, 7, 4, 4, 4, -51102806299971519682204621065844553633764265164800000⟩,
  ⟨3, 2, 8, 4, 5, 4, -99333813247932758952314558971510957544273923276800000⟩,
  ⟨3, 2, 5, 5, 1, 4, 21084378973780563476660251714663618815085196083200000⟩,
  ⟨3, 2, 6, 5, 2, 4, -166396694124059578408736590869571237777356147916800000⟩,
  ⟨3, 2, 7, 5, 3, 4, -58292158822423795589180662370635663621922331033600000⟩,
  ⟨3, 2, 8, 5, 4, 4, -49726735345842012656360375154997445400839218790400000⟩,
  ⟨3, 2, 5, 6, 0, 4, -1119555690595644840200994049503136876560614267289600000⟩,
  ⟨3, 2, 6, 6, 1, 4, 311628157198982654456193765509590915809990515097600000⟩,
  ⟨3, 2, 7, 6, 2, 4, -412562552894214853951827998280365653640309479833600000⟩,
  ⟨3, 2, 8, 6, 3, 4, 264019167360676236098301945565122527168260000972800000⟩,
  ⟨3, 2, 6, 7, 0, 4, 92470326154755202757511933280326407811522310963200000⟩,
  ⟨3, 2, 7, 7, 1, 4, 2134407166788198750690231017140093286485163035852800000⟩,
  ⟨3, 2, 8, 7, 2, 4, -103845768360510786758163795968032806261367190323200000⟩
]

def collectedFourData_10_1_28 : List CollectedFourTerm := [
  ⟨3, 3, 4, 0, 5, 5, -23458380130554369869731194180832709004455470694400000⟩,
  ⟨3, 3, 5, 0, 6, 5, -40920379602100354319703144579942504633515114496000000⟩,
  ⟨3, 3, 6, 0, 7, 5, -28173648469033828389217107891596087899642134528000000⟩,
  ⟨3, 3, 7, 0, 8, 5, -27547263666793137426317708675299902797025116160000000⟩,
  ⟨3, 3, 4, 1, 4, 5, -7218921958412021285356096365766680561587532595200000⟩,
  ⟨3, 3, 5, 1, 5, 5, 13412997226670463860418681537623794412830064640000000⟩,
  ⟨3, 3, 6, 1, 6, 5, 10382139276818387894823194555677536776909488128000000⟩,
  ⟨3, 3, 7, 1, 7, 5, 2179253742469695930442551551612258377059532800000000⟩,
  ⟨3, 3, 8, 1, 8, 5, 7873328778968222191405242296040792180765229056000000⟩,
  ⟨3, 3, 4, 2, 3, 5, -11334508036765922530726754499736317684519587020800000⟩,
  ⟨3, 3, 5, 2, 4, 5, -10075836153847960835049082025667662874478116864000000⟩,
  ⟨3, 3, 6, 2, 5, 5, 186525896098427105931566418917373085873078272000000⟩,
  ⟨3, 3, 7, 2, 6, 5, 1366821774641691552369537544088183161441222656000000⟩,
  ⟨3, 3, 8, 2, 7, 5, 3380628979298104223806197189709613689661816832000000⟩,
  ⟨3, 3, 4, 3, 2, 5, 30238392270254110678249708638072743630876757196800000⟩,
  ⟨3, 3, 5, 3, 3, 5, 3008700759006736388660400013293930922798743552000000⟩,
  ⟨3, 3, 6, 3, 4, 5, -3020360203040530449247271723464763383971053568000000⟩,
  ⟨3, 3, 7, 3, 5, 5, 3278303430727639442787538538952517308785885184000000⟩,
  ⟨3, 3, 8, 3, 6, 5, -181536157141848240847381575449984374344253440000000⟩,
  ⟨3, 3, 4, 4, 1, 5, -388206087586135723897915163422568576314245120000000⟩,
  ⟨3, 3, 5, 4, 2, 5, 6213824130845400230957666399581239262618583040000000⟩,
  ⟨3, 3, 6, 4, 3, 5, 3813536286589553212004076158075460942041186304000000⟩,
  ⟨3, 3, 7, 4, 4, 5, -1694898885804271251078621275229184634099073024000000⟩,
  ⟨3, 3, 8, 4, 5, 5, -2470912777397284860069954238787746213750898688000000⟩,
  ⟨3, 3, 4, 5, 0, 5, -124601971826443719134073647565919127541193585459200000⟩,
  ⟨3, 3, 5, 5, 1, 5, 2097882270149746976496582742618604499420315648000000⟩,
  ⟨3, 3, 6, 5, 2, 5, -8278182507734606112700920528819064786623922176000000⟩,
  ⟨3, 3, 7, 5, 3, 5, -1933344217131707185784559714539428653268205568000000⟩,
  ⟨3, 3, 8, 5, 4, 5, -1236944618622614738681999960045410572948209664000000⟩,
  ⟨3, 3, 5, 6, 0, 5, -111395077686024108064178662982848624614696812544000000⟩,
  ⟨3, 3, 6, 6, 1, 5, 15503401515410172882284733561798377601427832832000000⟩,
  ⟨3, 3, 7, 6, 2, 5, -13683237024604658206740035707471015605927149568000000⟩,
  ⟨3, 3, 8, 6, 3, 5, 6567434721155875567173024112310915051236098048000000⟩,
  ⟨3, 3, 6, 7, 0, 5, 4600369259067662067653569796228513098496999424000000⟩,
  ⟨3, 3, 7, 7, 1, 5, 70790717590082436591767252423156911602048958464000000⟩,
  ⟨3, 3, 8, 7, 2, 5, -2583146941919747394672491980767430523656077312000000⟩
]

def collectedFourData_10_1_29 : List CollectedFourTerm := [
  ⟨3, 4, 3, 0, 4, 6, -799507214512309626441208002278672670749255270400000⟩,
  ⟨3, 4, 4, 0, 5, 6, 47098574068571572835133363753081387082474271539200000⟩,
  ⟨3, 4, 5, 0, 6, 6, 41078955982414694819044158893637489601768587264000000⟩,
  ⟨3, 4, 6, 0, 7, 6, 18855218786290076875421962075625048006373408768000000⟩,
  ⟨3, 4, 7, 0, 8, 6, 13827007992199609055274645232148213832320286720000000⟩,
  ⟨3, 4, 3, 1, 3, 6, 3837772578598465786787735749359242739057269145600000⟩,
  ⟨3, 4, 4, 1, 4, 6, 14493794058297213599475580649494467198230043033600000⟩,
  ⟨3, 4, 5, 1, 5, 6, -13464975839040484894015684254121156360808693760000000⟩,
  ⟨3, 4, 6, 1, 6, 6, -6948248387116308071214469601579849057323450368000000⟩,
  ⟨3, 4, 7, 1, 7, 6, -1093849439226978548634827328541036744645017600000000⟩,
  ⟨3, 4, 8, 1, 8, 6, -3161535933842740513501420543991086562726746521600000⟩,
  ⟨3, 4, 3, 2, 2, 6, -2995049818151073773521856816990209490385528422400000⟩,
  ⟨3, 4, 4, 2, 3, 6, 22756864000388412439534222054324235685513815654400000⟩,
  ⟨3, 4, 5, 2, 4, 6, 10114882458927583434443058359078121912429182976000000⟩,
  ⟨3, 4, 6, 2, 5, 6, -124832486076847232206872811040095971450028032000000⟩,
  ⟨3, 4, 7, 2, 6, 6, -686059270005281792494102055336569183615844352000000⟩,
  ⟨3, 4, 8, 2, 7, 6, -1357491894100946288184151666114881244884054835200000⟩,
  ⟨3, 4, 3, 3, 1, 6, -67104691237806319280665176558771064180152729600000⟩,
  ⟨3, 4, 4, 3, 2, 6, -60711146725774748456989830062813936403970680422400000⟩,
  ⟨3, 4, 5, 3, 3, 6, -3020360203040530449247271723464763383971053568000000⟩,
  ⟨3, 4, 6, 3, 4, 6, 2021376553495618927096262247413962943924011008000000⟩,
  ⟨3, 4, 7, 3, 5, 6, -1645503825200921403650861292736973760708476928000000⟩,
  ⟨3, 4, 8, 3, 6, 6, 72895861484764262312313604392042910590173184000000⟩,
  ⟨3, 4, 3, 4, 0, 6, 12866878841846272604374476876050306583777352089600000⟩,
  ⟨3, 4, 4, 4, 1, 6, 779420960368498780897670899278645907591004160000000⟩,
  ⟨3, 4, 5, 4, 2, 6, -6237904204103781973889899798829423203304079360000000⟩,
  ⟨3, 4, 6, 4, 3, 6, -2552209775462145351118671480137525604724506624000000⟩,
  ⟨3, 4, 7, 4, 4, 6, 850733514713334740818297779459904057752158208000000⟩,
  ⟨3, 4, 8, 4, 5, 6, 992195265108236679139483032953615471740767436800000⟩,
  ⟨3, 4, 4, 5, 0, 6, 250169669282238769911130851227514868350808856985600000⟩,
  ⟨3, 4, 5, 5, 1, 6, -2106012071973699333708514288052502921039839232000000⟩,
  ⟨3, 4, 6, 5, 2, 6, 5540174979741564319259826796279020236367200256000000⟩,
  ⟨3, 4, 7, 5, 3, 6, 970418197077684898936387470583543100400992256000000⟩,
  ⟨3, 4, 8, 5, 4, 6, 496695231424246444748083301310618035384903270400000⟩,
  ⟨3, 4, 5, 6, 0, 6, 111826760587699286486673715072803654823990788096000000⟩,
  ⟨3, 4, 6, 6, 1, 6, -10375653967076866874880182343086934538051387392000000⟩,
  ⟨3, 4, 7, 6, 2, 6, 6868131440816726365958112463600515017663840256000000⟩,
  ⟨3, 4, 8, 6, 3, 6, -2637154048433086803471112761264596736092720332800000⟩,
  ⟨3, 4, 6, 7, 0, 6, -3078797869320422826311179406590659919393849344000000⟩,
  ⟨3, 4, 7, 7, 1, 6, -35532524381778759136622058739582838053628018688000000⟩,
  ⟨3, 4, 8, 7, 2, 6, 1037262904743766183433336085188662931460666163200000⟩
]

def collectedFourData_10_1_30 : List CollectedFourTerm := [
  ⟨3, 5, 2, 0, 3, 7, 7111703583231803019824149737547895111802893107200000⟩,
  ⟨3, 5, 3, 0, 4, 7, 2603358938700760957428199949953612411511085465600000⟩,
  ⟨3, 5, 4, 0, 5, 7, -76681292911327340342169649958238849558238357094400000⟩,
  ⟨3, 5, 5, 0, 6, 7, -44587159568680307082246158099986293889362296832000000⟩,
  ⟨3, 5, 6, 0, 7, 7, -15349111764547753601112738490842422850342617088000000⟩,
  ⟨3, 5, 7, 0, 8, 7, -9004712952824890515065701667426170883713007616000000⟩,
  ⟨3, 5, 2, 1, 2, 7, -6821640559185928824576235606997934411664588800000000⟩,
  ⟨3, 5, 3, 1, 3, 7, -12496572095712034968006618078630554810741843558400000⟩,
  ⟨3, 5, 4, 1, 4, 7, -23597378255287200577925789259993355481204863795200000⟩,
  ⟨3, 5, 5, 1, 5, 7, 14614904686982080594217275533153073143616634880000000⟩,
  ⟨3, 5, 6, 1, 6, 7, 5656229305556154420321826131918554601187442688000000⟩,
  ⟨3, 5, 7, 1, 7, 7, 712359479317875498727337650696709479889633280000000⟩,
  ⟨3, 5, 8, 1, 8, 7, 1715767888851746644568567001916766341290157670400000⟩,
  ⟨3, 5, 2, 2, 1, 7, -9452986658272711165767452442558167622721575321600000⟩,
  ⟨3, 5, 3, 2, 2, 7, 9752494504622931024828637270116192844905027993600000⟩,
  ⟨3, 5, 4, 2, 3, 7, -37050500756486028653293188527335021706960751820800000⟩,
  ⟨3, 5, 5, 2, 4, 7, -10978708378268267875298638332221887695487500288000000⟩,
  ⟨3, 5, 6, 2, 5, 7, 101620023737570322813845284561841103896051712000000⟩,
  ⟨3, 5, 7, 2, 6, 7, 446789847702936552296699327925679301166995865600000⟩,
  ⟨3, 5, 8, 2, 7, 7, 736711854621859997958802443628228422274960588800000⟩,
  ⟨3, 5, 2, 3, 0, 7, 16370325812400441347005556290938220454888236646400000⟩,
  ⟨3, 5, 3, 3, 1, 7, 218506593301051416532844067825116128534226534400000⟩,
  ⟨3, 5, 4, 3, 2, 7, 98843952648838582437935406281740011055807777996800000⟩,
  ⟨3, 5, 5, 3, 3, 7, 3278303430727639442787538538952517308785885184000000⟩,
  ⟨3, 5, 6, 3, 4, 7, -1645503825200921403650861292736973760708476928000000⟩,
  ⟨3, 5, 7, 3, 5, 7, 1071619371093781930420067545615997058299618918400000⟩,
  ⟨3, 5, 8, 3, 6, 7, -39560637925036032044577324940322468995792896000000⟩,
  ⟨3, 5, 3, 4, 0, 7, -41897187965380704904341751576919025982210729574400000⟩,
  ⟨3, 5, 4, 4, 1, 7, -1268976994425121343161920414930569329240965120000000⟩,
  ⟨3, 5, 5, 4, 2, 7, 6770630447414015594646147090965459633889607680000000⟩,
  ⟨3, 5, 6, 4, 3, 7, 2077629198268647639903276875333618238052368384000000⟩,
  ⟨3, 5, 7, 4, 4, 7, -554032448933498817143846534646578265322841702400000⟩,
  ⟨3, 5, 8, 4, 5, 7, -538465103976938404120907380514479748037161779200000⟩,
  ⟨3, 5, 4, 5, 0, 7, -407301793464743036043745210910092860397211300659200000⟩,
  ⟨3, 5, 5, 5, 1, 7, 2285868617178490735154751702156032998392201216000000⟩,
  ⟨3, 5, 6, 5, 2, 7, -4509985586644898178233727626681938174537629696000000⟩,
  ⟨3, 5, 7, 5, 3, 7, -631976007666450070292061657638251839406001356800000⟩,
  ⟨3, 5, 8, 5, 4, 7, -269556869337136380019351724119753586541959577600000⟩,
  ⟨3, 5, 5, 6, 0, 7, -121376931305333282100103103806890932895479758848000000⟩,
  ⟨3, 5, 6, 6, 1, 7, 8446312619121365197849554842632256083797737472000000⟩,
  ⟨3, 5, 7, 6, 2, 7, -4472808013253185719688041751039184848758295756800000⟩,
  ⟨3, 5, 8, 6, 3, 7, 1431185451925956712953087520573043942320452403200000⟩,
  ⟨3, 5, 6, 7, 0, 7, 2506298820091752181602056265176755257584123904000000⟩,
  ⟨3, 5, 7, 7, 1, 7, 23140232704549841092325046703950403491716294246400000⟩,
  ⟨3, 5, 8, 7, 2, 7, -562923345328950204046827340468506951167036620800000⟩
]

def collectedFourData_10_1_31 : List CollectedFourTerm := [
  ⟨3, 6, 1, 0, 2, 8, 1655994705926514365409294010316987760409313280000000⟩,
  ⟨3, 6, 2, 0, 3, 8, -1575243251897840978792958784844377255374225408000000⟩,
  ⟨3, 6, 3, 0, 4, 8, -288322168694262270805220373604278810225672192000000⟩,
  ⟨3, 6, 4, 0, 5, 8, 5661638724190575165977373385211134326626844672000000⟩,
  ⟨3, 6, 5, 0, 6, 8, 2469015384635112217107949484706367055981445120000000⟩,
  ⟨3, 6, 6, 0, 7, 8, 679966043206261695698753718653830407508721664000000⟩,
  ⟨3, 6, 7, 0, 8, 8, 332424178168772741105882081875402104546263040000000⟩,
  ⟨3, 6, 1, 1, 1, 8, -1636904483613482100989894414561073601336836096000000⟩,
  ⟨3, 6, 2, 1, 2, 8, 1510994255028696383795939464557677386924032000000000⟩,
  ⟨3, 6, 3, 1, 3, 8, 1383996157547924524296785397504206945793343488000000⟩,
  ⟨3, 6, 4, 1, 4, 8, 1742274099029586329811569138256644431807512576000000⟩,
  ⟨3, 6, 5, 1, 5, 8, -809300813646842374761371821780087237037260800000000⟩,
  ⟨3, 6, 6, 1, 6, 8, -250571102703781736530418894682432208543678464000000⟩,
  ⟨3, 6, 7, 1, 7, 8, -26297952606994628125582344144354974839603200000000⟩,
  ⟨3, 6, 8, 1, 8, 8, -54291829499381261421061730769849716790263808000000⟩,
  ⟨3, 6, 1, 2, 0, 8, -3107432636808517153215063811966461713426939904000000⟩,
  ⟨3, 6, 2, 2, 1, 8, 2093837752016871772534976482508911039400116224000000⟩,
  ⟨3, 6, 3, 2, 2, 8, -1080089389116297877923596133230083224373297152000000⟩,
  ⟨3, 6, 4, 2, 3, 8, 2735563549719267187321596962055508361692053504000000⟩,
  ⟨3, 6, 5, 2, 4, 8, 607946326960182696928696201315320781162414080000000⟩,
  ⟨3, 6, 6, 2, 5, 8, -4501769647085372588824601674405708862324736000000⟩,
  ⟨3, 6, 7, 2, 6, 8, -16494001387374160639269982567849736288600064000000⟩,
  ⟨3, 6, 8, 2, 7, 8, -23311681411680162832365545439324422931480576000000⟩,
  ⟨3, 6, 2, 3, 0, 8, -3626029258046526228492163545442938123290935296000000⟩,
  ⟨3, 6, 3, 3, 1, 8, -24199619160466360729330646044995762738167808000000⟩,
  ⟨3, 6, 4, 3, 2, 8, -7297982711583327524364407166983386651252752384000000⟩,
  ⟨3, 6, 5, 3, 3, 8, -181536157141848240847381575449984374344253440000000⟩,
  ⟨3, 6, 6, 3, 4, 8, 72895861484764262312313604392042910590173184000000⟩,
  ⟨3, 6, 7, 3, 5, 8, -39560637925036032044577324940322468995792896000000⟩,
  ⟨3, 6, 8, 3, 6, 8, 1251812336078984468873732647741281974353920000000⟩,
  ⟨3, 6, 3, 4, 0, 8, 4640116242441132925311283183271177991758020608000000⟩,
  ⟨3, 6, 4, 4, 1, 8, 93692855440664378195067578951415591704985600000000⟩,
  ⟨3, 6, 5, 4, 2, 8, -374923877189221498114291639789038598933708800000000⟩,
  ⟨3, 6, 6, 4, 3, 8, -92039026548723187725658120793364306541412352000000⟩,
  ⟨3, 6, 7, 4, 4, 8, 20453043032068366905088979400992060243705856000000⟩,
  ⟨3, 6, 8, 4, 5, 8, 17038584185211179175151452429935718678134784000000⟩,
  ⟨3, 6, 4, 5, 0, 8, 30072466422532370295630836631507362293424848896000000⟩,
  ⟨3, 6, 5, 5, 1, 8, -126580047656427336236646401760421130859970560000000⟩,
  ⟨3, 6, 6, 5, 2, 8, 199792476679418964617386520567883346779045888000000⟩,
  ⟨3, 6, 7, 5, 3, 8, 23330461067611898471443564235824822424174592000000⟩,
  ⟨3, 6, 8, 5, 4, 8, 8529554426055199469920174032792951982129152000000⟩,
  ⟨3, 6, 5, 6, 0, 8, 6721251446193818051985872273553251775471943680000000⟩,
  ⟨3, 6, 6, 6, 1, 8, -374171864757171469587171300319236931259990016000000⟩,
  ⟨3, 6, 7, 6, 2, 8, 165121257690501057326887295867321460134510592000000⟩,
  ⟨3, 6, 8, 6, 3, 8, -45286822910504348694346640901295342840971264000000⟩,
  ⟨3, 6, 6, 7, 0, 8, -111029101744280873952970168571130202829094912000000⟩,
  ⟨3, 6, 7, 7, 1, 8, -854260749869982829249543517346032575857033216000000⟩,
  ⟨3, 6, 8, 7, 2, 8, 17812513268489924724358273536974919844233216000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1005. -/
namespace LaughlinFock
def collectedFourData_10_1_32 : List CollectedFourTerm := [
  ⟨4, 0, 6, 0, 7, 3, 120021089212769463978440105534641714720178543001600000⟩,
  ⟨4, 0, 7, 0, 8, 3, 352057980039804708826657636447064046182445613056000000⟩,
  ⟨4, 0, 6, 1, 6, 3, -44228409598139271913157905949206144012728768921600000⟩,
  ⟨4, 0, 7, 1, 7, 3, -27851175341706119190771003120516363989790228480000000⟩,
  ⟨4, 0, 8, 1, 8, 3, -201244541718614634579298077786565757258567988019200000⟩,
  ⟨4, 0, 6, 2, 5, 3, -794609233544142969677005163853208864296429158400000⟩,
  ⟨4, 0, 7, 2, 6, 3, -17468178287153743341191701330421848506577295769600000⟩,
  ⟨4, 0, 8, 2, 7, 3, -86409846299937027036344708264337497320495408742400000⟩,
  ⟨4, 0, 6, 3, 4, 3, 12866878841846272604374476876050306583777352089600000⟩,
  ⟨4, 0, 7, 3, 5, 3, -41897187965380704904341751576919025982210729574400000⟩,
  ⟨4, 0, 8, 3, 6, 3, 4640116242441132925311283183271177991758020608000000⟩,
  ⟨4, 0, 6, 4, 3, 3, -16245846872547232436223708148114748134264720588800000⟩,
  ⟨4, 0, 7, 4, 4, 3, 21661050815267104234784712365722848615610082918400000⟩,
  ⟨4, 0, 8, 4, 5, 3, 63157239266102397776988228174749448195278477721600000⟩,
  ⟨4, 0, 6, 5, 2, 3, 35265453190148193938636398073444995514475164467200000⟩,
  ⟨4, 0, 7, 5, 3, 3, 24708416343562842335496413318062776018019339468800000⟩,
  ⟨4, 0, 8, 5, 4, 3, 31616659216743140729600273045180616444241300684800000⟩,
  ⟨4, 0, 6, 6, 1, 3, -66045231537108075836838104372430254608021349990400000⟩,
  ⟨4, 0, 7, 6, 2, 3, 174873731400596114335394908142171193747606129868800000⟩,
  ⟨4, 0, 8, 6, 3, 3, -167865515060979300740432347375541812028457458073600000⟩,
  ⟨4, 0, 6, 7, 0, 3, -19597792946877669996631701572281222460387151052800000⟩,
  ⟨4, 0, 7, 7, 1, 3, -904715522448621950916584539673393111616551544422400000⟩,
  ⟨4, 0, 8, 7, 2, 3, 66025976700874487875744329398236861744491685478400000⟩
]

def collectedFourData_10_1_33 : List CollectedFourTerm := [
  ⟨4, 1, 5, 0, 6, 4, 5279867205243499130732348572950362653993205760000000⟩,
  ⟨4, 1, 6, 0, 7, 4, 7270368654941571087208264757467983828599439360000000⟩,
  ⟨4, 1, 7, 0, 8, 4, 10663089793602362843432676781443776122768588800000000⟩,
  ⟨4, 1, 5, 1, 5, 4, -1730649736628650653909155291959141427734118400000000⟩,
  ⟨4, 1, 6, 1, 6, 4, -2679169510203187961086622654451444518077071360000000⟩,
  ⟨4, 1, 7, 1, 7, 4, -843553051950133146556741596667281150050304000000000⟩,
  ⟨4, 1, 8, 1, 8, 4, -4063513664378661255592545710771653427268157440000000⟩,
  ⟨4, 1, 5, 2, 4, 4, 1300063132145969806655313232481225914806435840000000⟩,
  ⟨4, 1, 6, 2, 5, 4, -48134057959139378754468735044803371875696640000000⟩,
  ⟨4, 1, 7, 2, 6, 4, -529074084858169797174692698638968820942766080000000⟩,
  ⟨4, 1, 8, 2, 7, 4, -1744780694065281858803218886898418850652487680000000⟩,
  ⟨4, 1, 5, 3, 3, 4, -388206087586135723897915163422568576314245120000000⟩,
  ⟨4, 1, 6, 3, 4, 4, 779420960368498780897670899278645907591004160000000⟩,
  ⟨4, 1, 7, 3, 5, 4, -1268976994425121343161920414930569329240965120000000⟩,
  ⟨4, 1, 8, 3, 6, 4, 93692855440664378195067578951415591704985600000000⟩,
  ⟨4, 1, 5, 4, 2, 4, -801756155896397069921897047216176541099622400000000⟩,
  ⟨4, 1, 6, 4, 3, 4, -984104515713572314229185322524206818635284480000000⟩,
  ⟨4, 1, 7, 4, 4, 4, 656067304143659041284322972189369462759096320000000⟩,
  ⟨4, 1, 8, 4, 5, 4, 1275265915639494911573807354432226289904517120000000⟩,
  ⟨4, 1, 5, 5, 1, 4, -270685167301255857582311414816988736656506880000000⟩,
  ⟨4, 1, 6, 5, 2, 4, 2136231616940567885174528379764795337993093120000000⟩,
  ⟨4, 1, 7, 5, 3, 4, 748365545071110970612478429969662196569866240000000⟩,
  ⟨4, 1, 8, 5, 4, 4, 638401050046246752679047502051180809667215360000000⟩,
  ⟨4, 1, 5, 6, 0, 4, 14373063574165916423377337547030490637811056640000000⟩,
  ⟨4, 1, 6, 6, 1, 4, -4000740072642681587937184165973552514560163840000000⟩,
  ⟨4, 1, 7, 6, 2, 4, 5296554562563898272739037746374009189291786240000000⟩,
  ⟨4, 1, 8, 6, 3, 4, -3389527032151831730318342844727892869927403520000000⟩,
  ⟨4, 1, 6, 7, 0, 4, -1187151195523854068637610048474194958488698880000000⟩,
  ⟨4, 1, 7, 7, 1, 4, -27401915026737371092687959183360899690287595520000000⟩,
  ⟨4, 1, 8, 7, 2, 4, 1333191232103532544462721657253446839833722880000000⟩
]

def collectedFourData_10_1_34 : List CollectedFourTerm := [
  ⟨4, 2, 4, 0, 5, 5, -48448237362729580644532747956432040299790860288000000⟩,
  ⟨4, 2, 5, 0, 6, 5, -84512240525650683834280962844770687990544465920000000⟩,
  ⟨4, 2, 6, 0, 7, 5, -58186609680861918490377965784233528321963458560000000⟩,
  ⟨4, 2, 7, 0, 8, 5, -56892946631219528044687954759790108704191283200000000⟩,
  ⟨4, 2, 4, 1, 4, 5, -14909130238222510761846432731276007698652463104000000⟩,
  ⟨4, 2, 5, 1, 5, 5, 27701660121747172297737274370651139208957132800000000⟩,
  ⟨4, 2, 6, 1, 6, 5, 21442075080071952452877468344427991351752130560000000⟩,
  ⟨4, 2, 7, 1, 7, 5, 4500779764041341467877271959352809625747456000000000⟩,
  ⟨4, 2, 8, 1, 8, 5, 16260666738085118870831437692894931911306117120000000⟩,
  ⟨4, 2, 4, 2, 3, 5, -23408987862710716408212999157908318137106825216000000⟩,
  ⟨4, 2, 5, 2, 4, 5, -20809471877121557541141848129403264271940321280000000⟩,
  ⟨4, 2, 6, 2, 5, 5, 385229109519885353450600087876663822977597440000000⟩,
  ⟨4, 2, 7, 2, 6, 5, 2822876319756484138960170103237082229107589120000000⟩,
  ⟨4, 2, 8, 2, 7, 5, 6981961853837782011329338579619777495055728640000000⟩,
  ⟨4, 2, 4, 3, 2, 5, 62450893796731123994260906225490963436442484736000000⟩,
  ⟨4, 2, 5, 3, 3, 5, 6213824130845400230957666399581239262618583040000000⟩,
  ⟨4, 2, 6, 3, 4, 5, -6237904204103781973889899798829423203304079360000000⟩,
  ⟨4, 2, 7, 3, 5, 5, 6770630447414015594646147090965459633889607680000000⟩,
  ⟨4, 2, 8, 3, 6, 5, -374923877189221498114291639789038598933708800000000⟩,
  ⟨4, 2, 4, 4, 1, 5, -801756155896397069921897047216176541099622400000000⟩,
  ⟨4, 2, 5, 4, 2, 5, 12833316910460533904983269371912649221917900800000000⟩,
  ⟨4, 2, 6, 4, 3, 5, 7876038762089357240033977786308757987346350080000000⟩,
  ⟨4, 2, 7, 4, 4, 5, -3500449010898123245862858244929689211088404480000000⟩,
  ⟨4, 2, 8, 4, 5, 5, -5103138753644027902690396208884140327315701760000000⟩,
  ⟨4, 2, 4, 5, 0, 5, -257338566146298883957317528588963372923967504384000000⟩,
  ⟨4, 2, 5, 5, 1, 5, 4332724494087861436108005928541157399157800960000000⟩,
  ⟨4, 2, 6, 5, 2, 5, -17096805015293451381637031919043777727582699520000000⟩,
  ⟨4, 2, 7, 5, 3, 5, -3992906544022483618631318350136078874559119360000000⟩,
  ⟨4, 2, 8, 5, 4, 5, -2554642995554665270410373856116979061258977280000000⟩,
  ⟨4, 2, 5, 6, 0, 5, -230062567608527265965505857711780860756104314880000000⟩,
  ⟨4, 2, 6, 6, 1, 5, 32018940454033097911608281191847316905672048640000000⟩,
  ⟨4, 2, 7, 6, 2, 5, -28259782285439065739724509327647774854201999360000000⟩,
  ⟨4, 2, 8, 6, 3, 5, 13563623509551865699861070008419183773047848960000000⟩,
  ⟨4, 2, 6, 7, 0, 5, 9501072988804337976515390721271170142285332480000000⟩,
  ⟨4, 2, 7, 7, 1, 5, 146202997384935781833839916116623066794326753280000000⟩,
  ⟨4, 2, 8, 7, 2, 5, -5334934274593470701173761165992460193879818240000000⟩
]

def collectedFourData_10_1_35 : List CollectedFourTerm := [
  ⟨4, 3, 3, 0, 4, 6, 1009465616340567478172026025209479033206813491200000⟩,
  ⟨4, 3, 4, 0, 5, 6, -59467119542997511726680745659541089976411855257600000⟩,
  ⟨4, 3, 5, 0, 6, 6, -51866690965021719547357579618003255887598190592000000⟩,
  ⟨4, 3, 6, 0, 7, 6, -23806783363360764908012059670072607024196091904000000⟩,
  ⟨4, 3, 7, 0, 8, 6, -17458115313575857562986651250721718022606684160000000⟩,
  ⟨4, 3, 3, 1, 3, 6, -4845609134112674817751262411842417655699786956800000⟩,
  ⟨4, 3, 4, 1, 4, 6, -18300005911887847376278971256406260753221078220800000⟩,
  ⟨4, 3, 5, 1, 5, 6, 17001009981703644421119223329064198914472673280000000⟩,
  ⟨4, 3, 6, 1, 6, 6, 8772926264169097596753644611214127503668936704000000⟩,
  ⟨4, 3, 7, 1, 7, 6, 1381104983557399935144896106336852600736972800000000⟩,
  ⟨4, 3, 8, 1, 8, 6, 3991786142900748300222664839422436616306478284800000⟩,
  ⟨4, 3, 3, 2, 2, 6, 3781579147468754210664824241752256124401431347200000⟩,
  ⟨4, 3, 4, 2, 3, 6, -28733038710780598982577465877031075574713627443200000⟩,
  ⟨4, 3, 5, 2, 4, 6, -12771149365852932705670245270843033052017328128000000⟩,
  ⟨4, 3, 6, 2, 5, 6, 157614715926931415201187870079458240412778496000000⟩,
  ⟨4, 3, 7, 2, 6, 6, 866225133771295913134218178668526290868371456000000⟩,
  ⟨4, 3, 8, 2, 7, 6, 1713982521585910739058343019232407505941928345600000⟩,
  ⟨4, 3, 3, 3, 1, 6, 84727038443344373169523237951443333335010508800000⟩,
  ⟨4, 3, 4, 3, 2, 6, 76654486708616490626156365124174217221355287347200000⟩,
  ⟨4, 3, 5, 3, 3, 6, 3813536286589553212004076158075460942041186304000000⟩,
  ⟨4, 3, 6, 3, 4, 6, -2552209775462145351118671480137525604724506624000000⟩,
  ⟨4, 3, 7, 3, 5, 6, 2077629198268647639903276875333618238052368384000000⟩,
  ⟨4, 3, 8, 3, 6, 6, -92039026548723187725658120793364306541412352000000⟩,
  ⟨4, 3, 3, 4, 0, 6, -16245846872547232436223708148114748134264720588800000⟩,
  ⟨4, 3, 4, 4, 1, 6, -984104515713572314229185322524206818635284480000000⟩,
  ⟨4, 3, 5, 4, 2, 6, 7876038762089357240033977786308757987346350080000000⟩,
  ⟨4, 3, 6, 4, 3, 6, 3222444985176114123168828017273748846828060672000000⟩,
  ⟨4, 3, 7, 4, 4, 6, -1074144443206211203509934178304845747243188224000000⟩,
  ⟨4, 3, 8, 4, 5, 6, -1252755430648159503131032794876690109238240870400000⟩,
  ⟨4, 3, 4, 5, 0, 6, -315866667376799375247371315874434514335738678476800000⟩,
  ⟨4, 3, 5, 5, 1, 6, 2659071407569986072145816026787472347125252096000000⟩,
  ⟨4, 3, 6, 5, 2, 6, -6995079029988293317698008257250603020182355968000000⟩,
  ⟨4, 3, 7, 5, 3, 6, -1225259491896736321284210596354295391970131968000000⟩,
  ⟨4, 3, 8, 5, 4, 6, -627132249493138217765470023444267522275357491200000⟩,
  ⟨4, 3, 5, 6, 0, 6, -141193559921644584638067017573652285450237247488000000⟩,
  ⟨4, 3, 6, 6, 1, 6, 13100402018511669590539183754734363244626968576000000⟩,
  ⟨4, 3, 7, 6, 2, 6, -8671769825418304816977063904370701789160275968000000⟩,
  ⟨4, 3, 8, 6, 3, 6, 3329696453721671062125874457102830617995142758400000⟩,
  ⟨4, 3, 6, 7, 0, 6, 3887320254686351045686540869393111086197112832000000⟩,
  ⟨4, 3, 7, 7, 1, 6, 44863712264395433983433660436973395395859185664000000⟩,
  ⟨4, 3, 8, 7, 2, 6, -1309658272543645520898331369526790448595179929600000⟩
]

def collectedFourData_10_1_36 : List CollectedFourTerm := [
  ⟨4, 4, 2, 0, 3, 7, -3676785488009098727411419561167070960119132979200000⟩,
  ⟨4, 4, 3, 0, 4, 7, -1345949286815450166232319209536136759006042521600000⟩,
  ⟨4, 4, 4, 0, 5, 7, 39644602967270999557060538547766780028632065638400000⟩,
  ⟨4, 4, 5, 0, 6, 7, 23051779272719767791060788040870536743225393152000000⟩,
  ⟨4, 4, 6, 0, 7, 7, 7935565751472550174525413061295282757952339968000000⟩,
  ⟨4, 4, 7, 0, 8, 7, 4655480578057011944339350602407713564079947776000000⟩,
  ⟨4, 4, 2, 1, 2, 7, 3526821487831345201988223912055078510185676800000000⟩,
  ⟨4, 4, 3, 1, 3, 7, 6460788810111439334403064188791910927341872742400000⟩,
  ⟨4, 4, 4, 1, 4, 7, 12199959813942860861053767786567375142578762547200000⟩,
  ⟨4, 4, 5, 1, 5, 7, -7555977106305722017856409388461508209074503680000000⟩,
  ⟨4, 4, 6, 1, 6, 7, -2924298177521889227752737959606940782787821568000000⟩,
  ⟨4, 4, 7, 1, 7, 7, -368293330163154921711502910076040983431086080000000⟩,
  ⟨4, 4, 8, 1, 8, 7, -887060378809447783469288308128194007394575974400000⟩,
  ⟨4, 4, 2, 2, 1, 7, 4887240273263207609082956704930393410783254937600000⟩,
  ⟨4, 4, 3, 2, 2, 7, -5042087292703367152208854990739233000400722329600000⟩,
  ⟨4, 4, 4, 2, 3, 7, 19155289855741124805518029038359588704111873228800000⟩,
  ⟨4, 4, 5, 2, 4, 7, 5676045854537262931915405461642545819358855168000000⟩,
  ⟨4, 4, 6, 2, 5, 7, -52538048611925705716387905360921448868216832000000⟩,
  ⟨4, 4, 7, 2, 6, 7, -230992533504529178108253965673985437022656921600000⟩,
  ⟨4, 4, 8, 2, 7, 7, -380883627138883487044827166406792176590441676800000⟩,
  ⟨4, 4, 2, 3, 0, 7, -8463538402097210772017713097792430902639748710400000⟩,
  ⟨4, 4, 3, 3, 1, 7, -112968975981774330034085645290492607540389478400000⟩,
  ⟨4, 4, 4, 3, 2, 7, -51102806299971519682204621065844553633764265164800000⟩,
  ⟨4, 4, 5, 3, 3, 7, -1694898885804271251078621275229184634099073024000000⟩,
  ⟨4, 4, 6, 3, 4, 7, 850733514713334740818297779459904057752158208000000⟩,
  ⟨4, 4, 7, 3, 5, 7, -554032448933498817143846534646578265322841702400000⟩,
  ⟨4, 4, 8, 3, 6, 7, 20453043032068366905088979400992060243705856000000⟩,
  ⟨4, 4, 3, 4, 0, 7, 21661050815267104234784712365722848615610082918400000⟩,
  ⟨4, 4, 4, 4, 1, 7, 656067304143659041284322972189369462759096320000000⟩,
  ⟨4, 4, 5, 4, 2, 7, -3500449010898123245862858244929689211088404480000000⟩,
  ⟨4, 4, 6, 4, 3, 7, -1074144443206211203509934178304845747243188224000000⟩,
  ⟨4, 4, 7, 4, 4, 7, 286437482142516547123941959910530240423028326400000⟩,
  ⟨4, 4, 8, 4, 5, 7, 278389088764863686906773435679960793959576371200000⟩,
  ⟨4, 4, 4, 5, 0, 7, 210577016593076693508161652773307799835782624051200000⟩,
  ⟨4, 4, 5, 5, 1, 7, -1181805239880082149475219689435514355765477376000000⟩,
  ⟨4, 4, 6, 5, 2, 7, 2331684576281316002985935782209999691271110656000000⟩,
  ⟨4, 4, 7, 5, 3, 7, 326734682704813803010620391323305689182162124800000⟩,
  ⟨4, 4, 8, 5, 4, 7, 139362218035746170527352570414762482606905753600000⟩,
  ⟨4, 4, 5, 6, 0, 7, 62752466322523959031276848187325436397331939328000000⟩,
  ⟨4, 4, 6, 6, 1, 7, -4366784878154464504581120409998727686433800192000000⟩,
  ⟨4, 4, 7, 6, 2, 7, 2312463589252505793248260101132290862995000524800000⟩,
  ⟨4, 4, 8, 6, 3, 7, -739929868941443376932944858238950254727869235200000⟩,
  ⟨4, 4, 6, 7, 0, 7, -1295768731426797189480657122823537986522578944000000⟩,
  ⟨4, 4, 7, 7, 1, 7, -11963613331389488575702041495323446619018782310400000⟩,
  ⟨4, 4, 8, 7, 2, 7, 291034119004500696289717946741762177440206028800000⟩
]

def collectedFourData_10_1_37 : List CollectedFourTerm := [
  ⟨4, 5, 1, 0, 2, 8, 22539964173521803300085276851997384862288838656000000⟩,
  ⟨4, 5, 2, 0, 3, 8, -21440845393581174392492549547360659013853878681600000⟩,
  ⟨4, 5, 3, 0, 4, 8, -3924391382135956915810490276248628149940020838400000⟩,
  ⟨4, 5, 4, 0, 5, 8, 77061317617728032919871821943916188002003871334400000⟩,
  ⟨4, 5, 5, 0, 6, 8, 33606096755250828545395103682743613849310593024000000⟩,
  ⟨4, 5, 6, 0, 7, 8, 9255108242937000487029933592935061739927293132800000⟩,
  ⟨4, 5, 7, 0, 8, 8, 4524669698230946270422453538278122147815620608000000⟩,
  ⟨4, 5, 1, 1, 1, 8, -22280124618805613134572321967673622015014810419200000⟩,
  ⟨4, 5, 2, 1, 2, 8, 20566343752704855680992206898047530383599206400000000⟩,
  ⟨4, 5, 3, 1, 3, 8, 18837755758384870408300145143012865025116838297600000⟩,
  ⟨4, 5, 4, 1, 4, 8, 23714324467366091022916817117717251409969361715200000⟩,
  ⟨4, 5, 5, 1, 5, 8, -11015501003667673270092724569661334135934812160000000⟩,
  ⟨4, 5, 6, 1, 6, 8, -3410556602415684001311201076898597278824844492800000⟩,
  ⟨4, 5, 7, 1, 7, 8, -357944930305192072251650818776682591829360640000000⟩,
  ⟨4, 5, 8, 1, 8, 8, -738973311600255645169473813327433931834366361600000⟩,
  ⟨4, 5, 1, 2, 0, 8, -42295678877855356563070309818695611558837144780800000⟩,
  ⟨4, 5, 2, 2, 1, 8, 28499504102715424887250447792015982639065124044800000⟩,
  ⟨4, 5, 3, 2, 2, 8, -14701240316623774569216122203159704551712777830400000⟩,
  ⟨4, 5, 4, 2, 3, 8, 37234119278519351487279342605257363473711287500800000⟩,
  ⟨4, 5, 5, 2, 4, 8, 8274838307191286473912985178095616075094818816000000⟩,
  ⟨4, 5, 6, 2, 5, 8, -61274185357966333183189755144736136397796147200000⟩,
  ⟨4, 5, 7, 2, 6, 8, -224502046424978230008355363675187193108548812800000⟩,
  ⟨4, 5, 8, 2, 7, 8, -317298395920803094793426353837198223579755315200000⟩,
  ⟨4, 5, 2, 3, 0, 8, -49354366457822108598786749514358312368990270259200000⟩,
  ⟨4, 5, 3, 3, 1, 8, -329384234706598488039570816272655446380747161600000⟩,
  ⟨4, 5, 4, 3, 2, 8, -99333813247932758952314558971510957544273923276800000⟩,
  ⟨4, 5, 5, 3, 3, 8, -2470912777397284860069954238787746213750898688000000⟩,
  ⟨4, 5, 6, 3, 4, 8, 992195265108236679139483032953615471740767436800000⟩,
  ⟨4, 5, 7, 3, 5, 8, -538465103976938404120907380514479748037161779200000⟩,
  ⟨4, 5, 8, 3, 6, 8, 17038584185211179175151452429935718678134784000000⟩,
  ⟨4, 5, 3, 4, 0, 8, 63157239266102397776988228174749448195278477721600000⟩,
  ⟨4, 5, 4, 4, 1, 8, 1275265915639494911573807354432226289904517120000000⟩,
  ⟨4, 5, 5, 4, 2, 8, -5103138753644027902690396208884140327315701760000000⟩,
  ⟨4, 5, 6, 4, 3, 8, -1252755430648159503131032794876690109238240870400000⟩,
  ⟨4, 5, 7, 4, 4, 8, 278389088764863686906773435679960793959576371200000⟩,
  ⟨4, 5, 8, 4, 5, 8, 231914435310542317611226630369033684461079756800000⟩,
  ⟨4, 5, 4, 5, 0, 8, 409320339822026087769373918040661663989198172979200000⟩,
  ⟨4, 5, 5, 5, 1, 8, -1722897862564279780559526134169986961990746112000000⟩,
  ⟨4, 5, 6, 5, 2, 8, 2719401970535726351596327241354078638160058777600000⟩,
  ⟨4, 5, 7, 5, 3, 8, 317554008315201154761606614060576890985801318400000⟩,
  ⟨4, 5, 8, 5, 4, 8, 116096899640644127617306607725789271608944230400000⟩,
  ⟨4, 5, 5, 6, 0, 8, 91483847295078862326053352882193511254365044736000000⟩,
  ⟨4, 5, 6, 6, 1, 8, -5092903012421070863567503917804379080242705203200000⟩,
  ⟨4, 5, 7, 6, 2, 8, 2247487397943356353589862113552154087379068518400000⟩,
  ⟨4, 5, 8, 6, 3, 8, -616404969340941437111837636628910351626063052800000⟩,
  ⟨4, 5, 6, 7, 0, 8, -1511231869629812627672852028066430153184929382400000⟩,
  ⟨4, 5, 7, 7, 1, 8, -11627456674834161269505589907795083964871553843200000⟩,
  ⟨4, 5, 8, 7, 2, 8, 242448486988074430611548333754931067908993843200000⟩
]

def collectedFourData_10_1_38 : List CollectedFourTerm := [
  ⟨5, 0, 5, 0, 6, 4, 1694671685459190136644044124846551090557848492441600000⟩,
  ⟨5, 0, 6, 0, 7, 4, 2333560186919753704297025102952715332114026437017600000⟩,
  ⟨5, 0, 7, 0, 8, 4, 3422517205504872949693151125036174163352703991808000000⟩,
  ⟨5, 0, 5, 1, 5, 4, -555484255967517080482798484767403545944070815744000000⟩,
  ⟨5, 0, 6, 1, 6, 4, -859929337801880833785693247565278042287995722137600000⟩,
  ⟨5, 0, 7, 1, 7, 4, -270754058151856025484814181690247499395775856640000000⟩,
  ⟨5, 0, 8, 1, 8, 4, -1304260369211586918445714888322540280058625812070400000⟩,
  ⟨5, 0, 5, 2, 4, 4, 417279468159570368916193915982570655344161613414400000⟩,
  ⟨5, 0, 6, 2, 5, 4, -15449522110820423861581441277531495156324656742400000⟩,
  ⟨5, 0, 7, 2, 6, 4, -169816178374513323710857772682077639923437718732800000⟩,
  ⟨5, 0, 8, 2, 7, 4, -560019849861338027031991194024083345761557597388800000⟩,
  ⟨5, 0, 5, 3, 3, 4, -124601971826443719134073647565919127541193585459200000⟩,
  ⟨5, 0, 6, 3, 4, 4, 250169669282238769911130851227514868350808856985600000⟩,
  ⟨5, 0, 7, 3, 5, 4, -407301793464743036043745210910092860397211300659200000⟩,
  ⟨5, 0, 8, 3, 6, 4, 30072466422532370295630836631507362293424848896000000⟩,
  ⟨5, 0, 5, 4, 2, 4, -257338566146298883957317528588963372923967504384000000⟩,
  ⟨5, 0, 6, 4, 3, 4, -315866667376799375247371315874434514335738678476800000⟩,
  ⟨5, 0, 7, 4, 4, 4, 210577016593076693508161652773307799835782624051200000⟩,
  ⟨5, 0, 8, 4, 5, 4, 409320339822026087769373918040661663989198172979200000⟩,
  ⟨5, 0, 5, 5, 1, 4, -86881444337020322762621442915444945780736838860800000⟩,
  ⟨5, 0, 6, 5, 2, 4, 685663311989477354756192275981896270477786297139200000⟩,
  ⟨5, 0, 7, 5, 3, 4, 240201855521242452776994150152842433041057343078400000⟩,
  ⟨5, 0, 8, 5, 4, 4, 204906703412230075875688204180704581276409633177600000⟩,
  ⟨5, 0, 5, 6, 0, 4, 4613302366440958615995147246819883106475193034342400000⟩,
  ⟨5, 0, 6, 6, 1, 4, -1284112016161364011139712719806739201352180065894400000⟩,
  ⟨5, 0, 7, 6, 2, 4, 1700027803493358830979566217222366564862392690278400000⟩,
  ⟨5, 0, 8, 6, 3, 4, -1087931810629945717569059725600660096549035127603200000⟩,
  ⟨5, 0, 6, 7, 0, 4, -381038279791455448542284757221599682859599973580800000⟩,
  ⟨5, 0, 7, 7, 1, 4, -8795154824548076351310039453913324380111118742323200000⟩,
  ⟨5, 0, 8, 7, 2, 4, 427912548653600374404231835069429106367068425420800000⟩
]

def collectedFourData_10_1_39 : List CollectedFourTerm := [
  ⟨5, 1, 4, 0, 5, 5, -16356867533270341127274107657095141721663707545600000⟩,
  ⟨5, 1, 5, 0, 6, 5, -28532627778969987071522002590556110832590127104000000⟩,
  ⟨5, 1, 6, 0, 7, 5, -19644691294633763545842344487703716395086774272000000⟩,
  ⟨5, 1, 7, 0, 8, 5, -19207930820206981614895388760691945705926819840000000⟩,
  ⟨5, 1, 4, 1, 4, 5, -5033550890965611176988674429249303711228677324800000⟩,
  ⟨5, 1, 5, 1, 5, 5, 9352505059588975540544711681737672011137679360000000⟩,
  ⟨5, 1, 6, 1, 6, 5, 7239173204533979398154059495476313370941980672000000⟩,
  ⟨5, 1, 7, 1, 7, 5, 1519532234901936156291565584432147576599347200000000⟩,
  ⟨5, 1, 8, 1, 8, 5, 5489850329253101917696678852279817966708588544000000⟩,
  ⟨5, 1, 4, 2, 3, 5, -7903233108184224736354591095638699293036196659200000⟩,
  ⟨5, 1, 5, 2, 4, 5, -7025596666871492008520577424158650769170497536000000⟩,
  ⟨5, 1, 6, 2, 5, 5, 130059252046676523515854533390060313984892928000000⟩,
  ⟨5, 1, 7, 2, 6, 5, 953046313725810326857599472764998029299154944000000⟩,
  ⟨5, 1, 8, 2, 7, 5, 2357217339209655090823142411614792213875130368000000⟩,
  ⟨5, 1, 4, 3, 2, 5, 21084378973780563476660251714663618815085196083200000⟩,
  ⟨5, 1, 5, 3, 3, 5, 2097882270149746976496582742618604499420315648000000⟩,
  ⟨5, 1, 6, 3, 4, 5, -2106012071973699333708514288052502921039839232000000⟩,
  ⟨5, 1, 7, 3, 5, 5, 2285868617178490735154751702156032998392201216000000⟩,
  ⟨5, 1, 8, 3, 6, 5, -126580047656427336236646401760421130859970560000000⟩,
  ⟨5, 1, 4, 4, 1, 5, -270685167301255857582311414816988736656506880000000⟩,
  ⟨5, 1, 5, 4, 2, 5, 4332724494087861436108005928541157399157800960000000⟩,
  ⟨5, 1, 6, 4, 3, 5, 2659071407569986072145816026787472347125252096000000⟩,
  ⟨5, 1, 7, 4, 4, 5, -1181805239880082149475219689435514355765477376000000⟩,
  ⟨5, 1, 8, 4, 5, 5, -1722897862564279780559526134169986961990746112000000⟩,
  ⟨5, 1, 4, 5, 0, 5, -86881444337020322762621442915444945780736838860800000⟩,
  ⟨5, 1, 5, 5, 1, 5, 1462794199866388907212197970116917819344945152000000⟩,
  ⟨5, 1, 6, 5, 2, 5, -5772143427707799314965515371281354259561447424000000⟩,
  ⟨5, 1, 7, 5, 3, 5, -1348066451299775176935649615124199713361887232000000⟩,
  ⟨5, 1, 8, 5, 4, 5, -862486632077761227728008443242544914535284736000000⟩,
  ⟨5, 1, 5, 6, 0, 5, -77672649152590733277211819623090742954196729856000000⟩,
  ⟨5, 1, 6, 6, 1, 5, 10810085073707690727250774803444676751542714368000000⟩,
  ⟨5, 1, 7, 6, 2, 5, -9540935656775436115640190105162487251685343232000000⟩,
  ⟨5, 1, 8, 6, 3, 5, 4579287195854996922009078759331482885792202752000000⟩,
  ⟨5, 1, 6, 7, 0, 5, 3207707870531490101728075288319835999332990976000000⟩,
  ⟨5, 1, 7, 7, 1, 5, 49360372871524660931333647734210034626447015936000000⟩,
  ⟨5, 1, 8, 7, 2, 5, -1801155583326936961933291962123627044051877888000000⟩
]

def collectedFourData_10_1_40 : List CollectedFourTerm := [
  ⟨5, 2, 3, 0, 4, 6, -2191283884392581917634213888076841152196431052800000⟩,
  ⟨5, 2, 4, 0, 5, 6, 129087448444459569928292150459004222321956644454400000⟩,
  ⟨5, 2, 5, 0, 6, 6, 112588920522557255701519436579138277248700776448000000⟩,
  ⟨5, 2, 6, 0, 7, 6, 51678254195988325944594998051757923813950488576000000⟩,
  ⟨5, 2, 7, 0, 8, 6, 37896968573518653120610339957249152675521495040000000⟩,
  ⟨5, 2, 3, 1, 3, 6, 10518540734590334577792726585361278114064446259200000⟩,
  ⟨5, 2, 4, 1, 4, 6, 39724491245554168116938682966530693234777338675200000⟩,
  ⟨5, 2, 5, 1, 5, 6, -36904713333728917054735117253102187594456760320000000⟩,
  ⟨5, 2, 6, 1, 6, 6, -19043711475114268417563532377150334635161419776000000⟩,
  ⟨5, 2, 7, 1, 7, 6, -2998015033037624424051054069133739790906163200000000⟩,
  ⟨5, 2, 8, 1, 8, 6, -8665115981453079153428423053658599300793578291200000⟩,
  ⟨5, 2, 3, 2, 2, 6, -8208811978602018767962672967922805508519283916800000⟩,
  ⟨5, 2, 4, 2, 3, 6, 62371856611429060434549305544657041306399067340800000⟩,
  ⟨5, 2, 5, 2, 4, 6, 27722800398109438371460759374878896498233311232000000⟩,
  ⟨5, 2, 6, 2, 5, 6, -342140020782320390663095924406777867900289024000000⟩,
  ⟨5, 2, 7, 2, 6, 6, -1880346536982458570610043281198790363016331264000000⟩,
  ⟨5, 2, 8, 2, 7, 6, -3720604463277380207215336041932444828483085926400000⟩,
  ⟨5, 2, 3, 3, 1, 6, -183920077026748455786739412566700114792624947200000⟩,
  ⟨5, 2, 4, 3, 2, 6, -166396694124059578408736590869571237777356147916800000⟩,
  ⟨5, 2, 5, 3, 3, 6, -8278182507734606112700920528819064786623922176000000⟩,
  ⟨5, 2, 6, 3, 4, 6, 5540174979741564319259826796279020236367200256000000⟩,
  ⟨5, 2, 7, 3, 5, 6, -4509985586644898178233727626681938174537629696000000⟩,
  ⟨5, 2, 8, 3, 6, 6, 199792476679418964617386520567883346779045888000000⟩,
  ⟨5, 2, 3, 4, 0, 6, 35265453190148193938636398073444995514475164467200000⟩,
  ⟨5, 2, 4, 4, 1, 6, 2136231616940567885174528379764795337993093120000000⟩,
  ⟨5, 2, 5, 4, 2, 6, -17096805015293451381637031919043777727582699520000000⟩,
  ⟨5, 2, 6, 4, 3, 6, -6995079029988293317698008257250603020182355968000000⟩,
  ⟨5, 2, 7, 4, 4, 6, 2331684576281316002985935782209999691271110656000000⟩,
  ⟨5, 2, 8, 4, 5, 6, 2719401970535726351596327241354078638160058777600000⟩,
  ⟨5, 2, 4, 5, 0, 6, 685663311989477354756192275981896270477786297139200000⟩,
  ⟨5, 2, 5, 5, 1, 6, -5772143427707799314965515371281354259561447424000000⟩,
  ⟨5, 2, 6, 5, 2, 6, 15184473547531413424466363592536510219201544192000000⟩,
  ⟨5, 2, 7, 5, 3, 6, 2659715531991481919450114836619883018234888192000000⟩,
  ⟨5, 2, 8, 5, 4, 6, 1361338880148201082403809770612456391225167052800000⟩,
  ⟨5, 2, 5, 6, 0, 6, 306494017654521305594917858013469120242827395072000000⟩,
  ⟨5, 2, 6, 6, 1, 6, -28437521157277116529237314024123401852675948544000000⟩,
  ⟨5, 2, 7, 6, 2, 6, 18824127498751893398168026068482875224534024192000000⟩,
  ⟨5, 2, 8, 6, 3, 6, -7227893710148759247651952569233904875213527449600000⟩,
  ⟨5, 2, 6, 7, 0, 6, -8438348062261529511789078692350427554809643008000000⟩,
  ⟨5, 2, 7, 7, 1, 6, -97387298871434365825294503804381236338429526016000000⟩,
  ⟨5, 2, 8, 7, 2, 6, 2842923047829804576124827963196390070647416422400000⟩
]

def collectedFourData_10_1_41 : List CollectedFourTerm := [
  ⟨5, 3, 2, 0, 3, 7, -4194050760439917620923952247766944791285622374400000⟩,
  ⟨5, 3, 3, 0, 4, 7, -1535302956425271403941765039302245699101602611200000⟩,
  ⟨5, 3, 4, 0, 5, 7, 45221968419009950105208187102570692495329250508800000⟩,
  ⟨5, 3, 5, 0, 6, 7, 26294798188129767788560443754516487386655883264000000⟩,
  ⟨5, 3, 6, 0, 7, 7, 9051973709922903705541908983738433464042520576000000⟩,
  ⟨5, 3, 7, 0, 8, 7, 5310432692440217776756203668422640109493420032000000⟩,
  ⟨5, 3, 2, 1, 2, 7, 4022989209246544690555329550499914341521817600000000⟩,
  ⟨5, 3, 3, 1, 3, 7, 7369719095786024708829054128379628577962642636800000⟩,
  ⟨5, 3, 4, 1, 4, 7, 13916300230696752267321772768651600913204930150400000⟩,
  ⟨5, 3, 5, 1, 5, 7, -8618982976275742936960936722713819838425333760000000⟩,
  ⟨5, 3, 6, 1, 6, 7, -3335700446813337210475891005681450848171851776000000⟩,
  ⟨5, 3, 7, 1, 7, 7, -420106347371415407379040550207012259558850560000000⟩,
  ⟨5, 3, 8, 1, 8, 7, -1011855673504735956450369414604174050565344460800000⟩,
  ⟨5, 3, 2, 2, 1, 7, 5574797292738178666861973212355117237071459123200000⟩,
  ⟨5, 3, 3, 2, 2, 7, -5751428826384301651285262307940938704305206067200000⟩,
  ⟨5, 3, 4, 2, 3, 7, 21850134648301053122579227514841531239536105881600000⟩,
  ⟨5, 3, 5, 2, 4, 7, 6474575280540527209815993262530831086021246976000000⟩,
  ⟨5, 3, 6, 2, 5, 7, -59929316913233825284874018353043080451457024000000⟩,
  ⟨5, 3, 7, 2, 6, 7, -263489511139578434236895435303524669714543411200000⟩,
  ⟨5, 3, 8, 2, 7, 7, -434467898997809368124235159204438671776913817600000⟩,
  ⟨5, 3, 2, 3, 0, 7, -9654223719901826092257994134232885987065515212800000⟩,
  ⟨5, 3, 3, 3, 1, 7, -128861915161395713912885738451583990422621388800000⟩,
  ⟨5, 3, 4, 3, 2, 7, -58292158822423795589180662370635663621922331033600000⟩,
  ⟨5, 3, 5, 3, 3, 7, -1933344217131707185784559714539428653268205568000000⟩,
  ⟨5, 3, 6, 3, 4, 7, 970418197077684898936387470583543100400992256000000⟩,
  ⟨5, 3, 7, 3, 5, 7, -631976007666450070292061657638251839406001356800000⟩,
  ⟨5, 3, 8, 3, 6, 7, 23330461067611898471443564235824822424174592000000⟩,
  ⟨5, 3, 3, 4, 0, 7, 24708416343562842335496413318062776018019339468800000⟩,
  ⟨5, 3, 4, 4, 1, 7, 748365545071110970612478429969662196569866240000000⟩,
  ⟨5, 3, 5, 4, 2, 7, -3992906544022483618631318350136078874559119360000000⟩,
  ⟨5, 3, 6, 4, 3, 7, -1225259491896736321284210596354295391970131968000000⟩,
  ⟨5, 3, 7, 4, 4, 7, 326734682704813803010620391323305689182162124800000⟩,
  ⟨5, 3, 8, 4, 5, 7, 317554008315201154761606614060576890985801318400000⟩,
  ⟨5, 3, 4, 5, 0, 7, 240201855521242452776994150152842433041057343078400000⟩,
  ⟨5, 3, 5, 5, 1, 7, -1348066451299775176935649615124199713361887232000000⟩,
  ⟨5, 3, 6, 5, 2, 7, 2659715531991481919450114836619883018234888192000000⟩,
  ⟨5, 3, 7, 5, 3, 7, 372701058826858714234517725499595694940985753600000⟩,
  ⟨5, 3, 8, 5, 4, 7, 158968266828616361245103952327606704637424435200000⟩,
  ⟨5, 3, 5, 6, 0, 7, 71580740828579618658553622681303089842902532096000000⟩,
  ⟨5, 3, 6, 6, 1, 7, -4981122096632889831335086282088073964283756544000000⟩,
  ⟨5, 3, 7, 6, 2, 7, 2637790457622175182604002426084511928741894553600000⟩,
  ⟨5, 3, 8, 6, 3, 7, -844026239666878714963819777122609809731249766400000⟩,
  ⟨5, 3, 6, 7, 0, 7, -1478062794557401071867889031057824552486699008000000⟩,
  ⟨5, 3, 7, 7, 1, 7, -13646703554982877232141144625195181828370910412800000⟩,
  ⟨5, 3, 8, 7, 2, 7, 331977993305702214158352995119372719370115481600000⟩
]

def collectedFourData_10_1_42 : List CollectedFourTerm := [
  ⟨5, 4, 1, 0, 2, 8, 11283557899503119482351002190422054580852359168000000⟩,
  ⟨5, 4, 2, 0, 3, 8, -10733336510666122824875037160044071881177615564800000⟩,
  ⟨5, 4, 3, 0, 4, 8, -1964559350660376418232390203747541779119026995200000⟩,
  ⟨5, 4, 4, 0, 5, 8, 38577072814209943625263297217646736710034469683200000⟩,
  ⟨5, 4, 5, 0, 6, 8, 16823289318251313011014437291404929038519631872000000⟩,
  ⟨5, 4, 6, 0, 7, 8, 4633128470009953034352241790253545331913811558400000⟩,
  ⟨5, 4, 7, 0, 8, 8, 2265060056133136861666628853288789804186599424000000⟩,
  ⟨5, 4, 1, 1, 1, 8, -11153481620869747656535490120069611448253913497600000⟩,
  ⟨5, 4, 2, 1, 2, 8, 10295558978187611359101133146760068264571699200000000⟩,
  ⟨5, 4, 3, 1, 3, 8, 9430223853067579584231582559565332663346449612800000⟩,
  ⟨5, 4, 4, 1, 4, 8, 11871445363230134508226462251782959956823218585600000⟩,
  ⟨5, 4, 5, 1, 5, 8, -5514385134335301656181154859081569111879188480000000⟩,
  ⟨5, 4, 6, 1, 6, 8, -1707332478287480880695804430662301173267457638400000⟩,
  ⟨5, 4, 7, 1, 7, 8, -179188055262164974029524002563528511633489920000000⟩,
  ⟨5, 4, 8, 1, 8, 8, -369931739173932234589077586382957018815974604800000⟩,
  ⟨5, 4, 1, 2, 0, 8, -21173314111905431537176821456952826898963392102400000⟩,
  ⟨5, 4, 2, 2, 1, 8, 14266917292968834350310907211040083302116910694400000⟩,
  ⟨5, 4, 3, 2, 2, 8, -7359474710345793360145407138607970613808280371200000⟩,
  ⟨5, 4, 4, 2, 3, 8, 18639485736615251147346802218009371338795804262400000⟩,
  ⟨5, 4, 5, 2, 4, 8, 4142403085888779942287659142861031022314651648000000⟩,
  ⟨5, 4, 6, 2, 5, 8, -30673998099947805287430510702343977761872281600000⟩,
  ⟨5, 4, 7, 2, 6, 8, -112386240718561751735521220016935779244074598400000⟩,
  ⟨5, 4, 8, 2, 7, 8, -158840306676159273910142792506070425000319385600000⟩,
  ⟨5, 4, 2, 3, 0, 8, -24706909347013286412312784500615443618303941017600000⟩,
  ⟨5, 4, 3, 3, 1, 8, -164890505365639940893086226942713177932877004800000⟩,
  ⟨5, 4, 4, 3, 2, 8, -49726735345842012656360375154997445400839218790400000⟩,
  ⟨5, 4, 5, 3, 3, 8, -1236944618622614738681999960045410572948209664000000⟩,
  ⟨5, 4, 6, 3, 4, 8, 496695231424246444748083301310618035384903270400000⟩,
  ⟨5, 4, 7, 3, 5, 8, -269556869337136380019351724119753586541959577600000⟩,
  ⟨5, 4, 8, 3, 6, 8, 8529554426055199469920174032792951982129152000000⟩,
  ⟨5, 4, 3, 4, 0, 8, 31616659216743140729600273045180616444241300684800000⟩,
  ⟨5, 4, 4, 4, 1, 8, 638401050046246752679047502051180809667215360000000⟩,
  ⟨5, 4, 5, 4, 2, 8, -2554642995554665270410373856116979061258977280000000⟩,
  ⟨5, 4, 6, 4, 3, 8, -627132249493138217765470023444267522275357491200000⟩,
  ⟨5, 4, 7, 4, 4, 8, 139362218035746170527352570414762482606905753600000⟩,
  ⟨5, 4, 8, 4, 5, 8, 116096899640644127617306607725789271608944230400000⟩,
  ⟨5, 4, 4, 5, 0, 8, 204906703412230075875688204180704581276409633177600000⟩,
  ⟨5, 4, 5, 5, 1, 8, -862486632077761227728008443242544914535284736000000⟩,
  ⟨5, 4, 6, 5, 2, 8, 1361338880148201082403809770612456391225167052800000⟩,
  ⟨5, 4, 7, 5, 3, 8, 158968266828616361245103952327606704637424435200000⟩,
  ⟨5, 4, 8, 5, 4, 8, 58118374943420747904527325302329868582859571200000⟩,
  ⟨5, 4, 5, 6, 0, 8, 45797024337596188613436426565897733988478353408000000⟩,
  ⟨5, 4, 6, 6, 1, 8, -2549518959959735539238118920353022017357322649600000⟩,
  ⟨5, 4, 7, 6, 2, 8, 1125097359865727685381322231753957791965066035200000⟩,
  ⟨5, 4, 8, 6, 3, 8, -308573745173492078884764681030534357359945318400000⟩,
  ⟨5, 4, 6, 7, 0, 8, -756526149255099032740877225751989066071749427200000⟩,
  ⟨5, 4, 7, 7, 1, 8, -5820731550610792444175360716024090724662876569600000⟩,
  ⟨5, 4, 8, 7, 2, 8, 121370270135146550221995612806076508143196569600000⟩
]

def collectedFourData_10_1_43 : List CollectedFourTerm := [
  ⟨6, 0, 4, 0, 5, 5, 868530401107110443506212556194925609449052490956800000⟩,
  ⟨6, 0, 5, 0, 6, 5, 1515048929698946937022109148483524419512919130112000000⟩,
  ⟨6, 0, 6, 0, 7, 5, 1043109970478699472660846173627852112583999881216000000⟩,
  ⟨6, 0, 7, 0, 8, 5, 1019918503697542460005714574512378063695139307520000000⟩,
  ⟨6, 0, 4, 1, 4, 5, 267275623858361892356820214108672033499963090534400000⟩,
  ⟨6, 0, 5, 1, 5, 5, -496607003403237715095269296323509143201728430080000000⟩,
  ⟨6, 0, 6, 1, 6, 5, -384391570955068536517550710449468888698811580416000000⟩,
  ⟨6, 0, 7, 1, 7, 5, -80685371987645722941306772822844404569577881600000000⟩,
  ⟨6, 0, 8, 1, 8, 5, -291504586607780609949558616226531491685892882432000000⟩,
  ⟨6, 0, 4, 2, 3, 5, 419652369717628537378340401767131265903149816217600000⟩,
  ⟨6, 0, 5, 2, 4, 5, 373050908352907068897657739953608563305436151808000000⟩,
  ⟨6, 0, 6, 2, 5, 5, -6905993101553582282428310402070145471698960384000000⟩,
  ⟨6, 0, 7, 2, 6, 5, -50605636773071877129143232526427128979502661632000000⟩,
  ⟨6, 0, 8, 2, 7, 5, -125165464411575117021691620194868513057175240704000000⟩,
  ⟨6, 0, 4, 3, 2, 5, -1119555690595644840200994049503136876560614267289600000⟩,
  ⟨6, 0, 5, 3, 3, 5, -111395077686024108064178662982848624614696812544000000⟩,
  ⟨6, 0, 6, 3, 4, 5, 111826760587699286486673715072803654823990788096000000⟩,
  ⟨6, 0, 7, 3, 5, 5, -121376931305333282100103103806890932895479758848000000⟩,
  ⟨6, 0, 8, 3, 6, 5, 6721251446193818051985872273553251775471943680000000⟩,
  ⟨6, 0, 4, 4, 1, 5, 14373063574165916423377337547030490637811056640000000⟩,
  ⟨6, 0, 5, 4, 2, 5, -230062567608527265965505857711780860756104314880000000⟩,
  ⟨6, 0, 6, 4, 3, 5, -141193559921644584638067017573652285450237247488000000⟩,
  ⟨6, 0, 7, 4, 4, 5, 62752466322523959031276848187325436397331939328000000⟩,
  ⟨6, 0, 8, 4, 5, 5, 91483847295078862326053352882193511254365044736000000⟩,
  ⟨6, 0, 4, 5, 0, 5, 4613302366440958615995147246819883106475193034342400000⟩,
  ⟨6, 0, 5, 5, 1, 5, -77672649152590733277211819623090742954196729856000000⟩,
  ⟨6, 0, 6, 5, 2, 5, 306494017654521305594917858013469120242827395072000000⟩,
  ⟨6, 0, 7, 5, 3, 5, 71580740828579618658553622681303089842902532096000000⟩,
  ⟨6, 0, 8, 5, 4, 5, 45797024337596188613436426565897733988478353408000000⟩,
  ⟨6, 0, 5, 6, 0, 5, 4124326188149029908159917846435366329245675552768000000⟩,
  ⟨6, 0, 6, 6, 1, 5, -574002785433828311644562939639822691342382792704000000⟩,
  ⟨6, 0, 7, 6, 2, 5, 506612446182689493713110793132764485257156100096000000⟩,
  ⟨6, 0, 8, 6, 3, 5, -243154756673963018637558807137708707201633222656000000⟩,
  ⟨6, 0, 6, 7, 0, 5, -170325509927885787168890359878710527632372400128000000⟩,
  ⟨6, 0, 7, 7, 1, 5, -2620977663461602639970515260982722680998758187008000000⟩,
  ⟨6, 0, 8, 7, 2, 5, 95639240096632555337092875442789923672255627264000000⟩
]

def collectedFourData_10_1_44 : List CollectedFourTerm := [
  ⟨6, 1, 3, 0, 4, 6, 4103842100877123980339123731964914523522570649600000⟩,
  ⟨6, 1, 4, 0, 5, 6, -241755305825208008444395200505493963320601660620800000⟩,
  ⟨6, 1, 5, 0, 6, 6, -210856820252140517672128829942750796220974759936000000⟩,
  ⟨6, 1, 6, 0, 7, 6, -96783167521041950782306537291727655343994437632000000⟩,
  ⟨6, 1, 7, 0, 8, 6, -70973540322792884268954547559254948884806369280000000⟩,
  ⟨6, 1, 3, 1, 3, 6, -19699150171210438866138466172175066112201221734400000⟩,
  ⟨6, 1, 4, 1, 4, 6, -74396129488543877616471346114474758685187270246400000⟩,
  ⟨6, 1, 5, 1, 5, 6, 69115242154824652809015273696814795006924554240000000⟩,
  ⟨6, 1, 6, 1, 6, 6, 35665111884941538243773500218584331506556076032000000⟩,
  ⟨6, 1, 7, 1, 7, 6, 5614690273256305753904011286742062997071462400000000⟩,
  ⟨6, 1, 8, 1, 8, 6, 16228051521278612588260070292126149405183469158400000⟩,
  ⟨6, 1, 3, 2, 2, 6, 15373484209833242076482404060134409466206067097600000⟩,
  ⟨6, 1, 4, 2, 3, 6, -116810173658903342955771799707699726071570733465600000⟩,
  ⟨6, 1, 5, 2, 4, 6, -51919331967118148038893856299746508596601421824000000⟩,
  ⟨6, 1, 6, 2, 5, 6, 640760711874020930252682953886748450454765568000000⟩,
  ⟨6, 1, 7, 2, 6, 6, 3521517836036178896780536617808495623429685248000000⟩,
  ⟨6, 1, 8, 2, 7, 6, 6967957618755322395374989004999595894206418124800000⟩,
  ⟨6, 1, 3, 3, 1, 6, 344445993818896073357305289089070013266421350400000⟩,
  ⟨6, 1, 4, 3, 2, 6, 311628157198982654456193765509590915809990515097600000⟩,
  ⟨6, 1, 5, 3, 3, 6, 15503401515410172882284733561798377601427832832000000⟩,
  ⟨6, 1, 6, 3, 4, 6, -10375653967076866874880182343086934538051387392000000⟩,
  ⟨6, 1, 7, 3, 5, 6, 8446312619121365197849554842632256083797737472000000⟩,
  ⟨6, 1, 8, 3, 6, 6, -374171864757171469587171300319236931259990016000000⟩,
  ⟨6, 1, 3, 4, 0, 6, -66045231537108075836838104372430254608021349990400000⟩,
  ⟨6, 1, 4, 4, 1, 6, -4000740072642681587937184165973552514560163840000000⟩,
  ⟨6, 1, 5, 4, 2, 6, 32018940454033097911608281191847316905672048640000000⟩,
  ⟨6, 1, 6, 4, 3, 6, 13100402018511669590539183754734363244626968576000000⟩,
  ⟨6, 1, 7, 4, 4, 6, -4366784878154464504581120409998727686433800192000000⟩,
  ⟨6, 1, 8, 4, 5, 6, -5092903012421070863567503917804379080242705203200000⟩,
  ⟨6, 1, 4, 5, 0, 6, -1284112016161364011139712719806739201352180065894400000⟩,
  ⟨6, 1, 5, 5, 1, 6, 10810085073707690727250774803444676751542714368000000⟩,
  ⟨6, 1, 6, 5, 2, 6, -28437521157277116529237314024123401852675948544000000⟩,
  ⟨6, 1, 7, 5, 3, 6, -4981122096632889831335086282088073964283756544000000⟩,
  ⟨6, 1, 8, 5, 4, 6, -2549518959959735539238118920353022017357322649600000⟩,
  ⟨6, 1, 5, 6, 0, 6, -574002785433828311644562939639822691342382792704000000⟩,
  ⟨6, 1, 6, 6, 1, 6, 53257862845172875831217951330915160949373534208000000⟩,
  ⟨6, 1, 7, 6, 2, 6, -35253874448618350530960239360470328220051308544000000⟩,
  ⟨6, 1, 8, 6, 3, 6, 13536417950974754417853574706495175208591373107200000⟩,
  ⟨6, 1, 6, 7, 0, 6, 15803359978327504596102177843582601020473081856000000⟩,
  ⟨6, 1, 7, 7, 1, 6, 182387184082303807333754841552078391962041843712000000⟩,
  ⟨6, 1, 8, 7, 2, 6, -5324233604023377098676282642470827782189141196800000⟩
]

def collectedFourData_10_1_45 : List CollectedFourTerm := [
  ⟨6, 2, 2, 0, 3, 7, -29683379782966650120397092102948926654612137574400000⟩,
  ⟨6, 2, 3, 0, 4, 7, -10866101375631095010260707340823075604315452211200000⟩,
  ⟨6, 2, 4, 0, 5, 7, 320058325420457472372299847721612768389836360908800000⟩,
  ⟨6, 2, 5, 0, 6, 7, 186101343430771923024810084232285619703213195264000000⟩,
  ⟨6, 2, 6, 0, 7, 7, 64065312692802908318824670970960022590587928576000000⟩,
  ⟨6, 2, 7, 0, 8, 7, 37584569053964192078132633283501564102319276032000000⟩,
  ⟨6, 2, 2, 1, 2, 7, 28472692244744371212821487410838720162142617600000000⟩,
  ⟨6, 2, 3, 1, 3, 7, 52159161466861314971198197589383300531069177036800000⟩,
  ⟨6, 2, 4, 1, 4, 7, 98492566856350944505075004707238628571134453350400000⟩,
  ⟨6, 2, 5, 1, 5, 7, -61000822269705142499619978975957332967303413760000000⟩,
  ⟨6, 2, 6, 1, 6, 7, -23608408400518757780259156262074609178326859776000000⟩,
  ⟨6, 2, 7, 1, 7, 7, -2973301223696355358075277700955748726011330560000000⟩,
  ⟨6, 2, 8, 1, 8, 7, -7161405037224717450276270931643486824825670860800000⟩,
  ⟨6, 2, 2, 2, 1, 7, 39455608600226967464297135810949244857387004723200000⟩,
  ⟨6, 2, 3, 2, 2, 7, -40705717670036073833790582586501631340631503667200000⟩,
  ⟨6, 2, 4, 2, 3, 7, 154644252566568332262602744312529618368160438681600000⟩,
  ⟨6, 2, 5, 2, 4, 7, 45823784203683224438921801606917583311497854976000000⟩,
  ⟨6, 2, 6, 2, 5, 7, -424149533631942834511062195479048479806849024000000⟩,
  ⟨6, 2, 7, 2, 6, 7, -1864846105764335045925858010258787367094793011200000⟩,
  ⟨6, 2, 8, 2, 7, 7, -3074945055769150632201262832230625914333534617600000⟩,
  ⟨6, 2, 2, 3, 0, 7, -68327735060009711833404939140836959671133457612800000⟩,
  ⟨6, 2, 3, 3, 1, 7, -912019759840704365743969851790335738200771788800000⟩,
  ⟨6, 2, 4, 3, 2, 7, -412562552894214853951827998280365653640309479833600000⟩,
  ⟨6, 2, 5, 3, 3, 7, -13683237024604658206740035707471015605927149568000000⟩,
  ⟨6, 2, 6, 3, 4, 7, 6868131440816726365958112463600515017663840256000000⟩,
  ⟨6, 2, 7, 3, 5, 7, -4472808013253185719688041751039184848758295756800000⟩,
  ⟨6, 2, 8, 3, 6, 7, 165121257690501057326887295867321460134510592000000⟩,
  ⟨6, 2, 3, 4, 0, 7, 174873731400596114335394908142171193747606129868800000⟩,
  ⟨6, 2, 4, 4, 1, 7, 5296554562563898272739037746374009189291786240000000⟩,
  ⟨6, 2, 5, 4, 2, 7, -28259782285439065739724509327647774854201999360000000⟩,
  ⟨6, 2, 6, 4, 3, 7, -8671769825418304816977063904370701789160275968000000⟩,
  ⟨6, 2, 7, 4, 4, 7, 2312463589252505793248260101132290862995000524800000⟩,
  ⟨6, 2, 8, 4, 5, 7, 2247487397943356353589862113552154087379068518400000⟩,
  ⟨6, 2, 4, 5, 0, 7, 1700027803493358830979566217222366564862392690278400000⟩,
  ⟨6, 2, 5, 5, 1, 7, -9540935656775436115640190105162487251685343232000000⟩,
  ⟨6, 2, 6, 5, 2, 7, 18824127498751893398168026068482875224534024192000000⟩,
  ⟨6, 2, 7, 5, 3, 7, 2637790457622175182604002426084511928741894553600000⟩,
  ⟨6, 2, 8, 5, 4, 7, 1125097359865727685381322231753957791965066035200000⟩,
  ⟨6, 2, 5, 6, 0, 7, 506612446182689493713110793132764485257156100096000000⟩,
  ⟨6, 2, 6, 6, 1, 7, -35253874448618350530960239360470328220051308544000000⟩,
  ⟨6, 2, 7, 6, 2, 7, 18668952860568531065191461595358567392853203353600000⟩,
  ⟨6, 2, 8, 6, 3, 7, -5973592798431772770613992844246562220630500966400000⟩,
  ⟨6, 2, 6, 7, 0, 7, -10460984327552196067260351396637083612645163008000000⟩,
  ⟨6, 2, 7, 7, 1, 7, -96584497314388400188674062653819961855760452812800000⟩,
  ⟨6, 2, 8, 7, 2, 7, 2349573101935156456491863429842518559751248281600000⟩
]

def collectedFourData_10_1_46 : List CollectedFourTerm := [
  ⟨6, 3, 1, 0, 2, 8, -59908931096597619089274501323259834772777598976000000⟩,
  ⟨6, 3, 2, 0, 3, 8, 56987585226323719135975243036695141167518030233600000⟩,
  ⟨6, 3, 3, 0, 4, 8, 10430632945932047674861163206909398155585283686400000⟩,
  ⟨6, 3, 4, 0, 5, 8, -204821140434499330369067339263266641738436339302400000⟩,
  ⟨6, 3, 5, 0, 6, 8, -89321585404336587914553346671493849940496482304000000⟩,
  ⟨6, 3, 6, 0, 7, 8, -24599135905859432526026668391348083280250195148800000⟩,
  ⟨6, 3, 7, 0, 8, 8, -12026111625528254004494380016564178053253562368000000⟩,
  ⟨6, 3, 1, 1, 1, 8, 59218304001548843297146685157705890352493441843200000⟩,
  ⟨6, 3, 2, 1, 2, 8, -54663248854544336750428255482650833751271014400000000⟩,
  ⟨6, 3, 3, 1, 3, 8, -50068837867512973493196212804344067168193321369600000⟩,
  ⟨6, 3, 4, 1, 4, 8, -63030261254218045130077632599851601306970174259200000⟩,
  ⟨6, 3, 5, 1, 5, 8, 29278080725543447639782038446207749624021647360000000⟩,
  ⟨6, 3, 6, 1, 6, 8, 9064912389487727182426808953030033363696405708800000⟩,
  ⟨6, 3, 7, 1, 7, 8, 951381200118367862543636735818312705313341440000000⟩,
  ⟨6, 3, 8, 1, 8, 8, 1964115863985734444421032753168142217661487513600000⟩,
  ⟨6, 3, 1, 2, 0, 8, 112417610430537927083171212384029616324263857356800000⟩,
  ⟨6, 3, 2, 2, 1, 8, -75748781783001708919419077846373571923112938700800000⟩,
  ⟨6, 3, 3, 2, 2, 8, 39074400756934491716949588067285267891500770918400000⟩,
  ⟨6, 3, 4, 2, 3, 8, -98964500082023838400228873920899608068664118476800000⟩,
  ⟨6, 3, 5, 2, 4, 8, -21993678169345193579004426170157513093295374336000000⟩,
  ⟨6, 3, 6, 2, 5, 8, 162860549393543820877390256664445232811815731200000⟩,
  ⟨6, 3, 7, 2, 6, 8, 596703593971050573190656818820502607331380428800000⟩,
  ⟨6, 3, 8, 2, 7, 8, 843346847933797844417408445359330308620759859200000⟩,
  ⟨6, 3, 2, 3, 0, 8, 131178883722950797406143223870292500816113906483200000⟩,
  ⟨6, 3, 3, 3, 1, 8, 875469777566195419161112793827199748872444313600000⟩,
  ⟨6, 3, 4, 3, 2, 8, 264019167360676236098301945565122527168260000972800000⟩,
  ⟨6, 3, 5, 3, 3, 8, 6567434721155875567173024112310915051236098048000000⟩,
  ⟨6, 3, 6, 3, 4, 8, -2637154048433086803471112761264596736092720332800000⟩,
  ⟨6, 3, 7, 3, 5, 8, 1431185451925956712953087520573043942320452403200000⟩,
  ⟨6, 3, 8, 3, 6, 8, -45286822910504348694346640901295342840971264000000⟩,
  ⟨6, 3, 3, 4, 0, 8, -167865515060979300740432347375541812028457458073600000⟩,
  ⟨6, 3, 4, 4, 1, 8, -3389527032151831730318342844727892869927403520000000⟩,
  ⟨6, 3, 5, 4, 2, 8, 13563623509551865699861070008419183773047848960000000⟩,
  ⟨6, 3, 6, 4, 3, 8, 3329696453721671062125874457102830617995142758400000⟩,
  ⟨6, 3, 7, 4, 4, 8, -739929868941443376932944858238950254727869235200000⟩,
  ⟨6, 3, 8, 4, 5, 8, -616404969340941437111837636628910351626063052800000⟩,
  ⟨6, 3, 4, 5, 0, 8, -1087931810629945717569059725600660096549035127603200000⟩,
  ⟨6, 3, 5, 5, 1, 8, 4579287195854996922009078759331482885792202752000000⟩,
  ⟨6, 3, 6, 5, 2, 8, -7227893710148759247651952569233904875213527449600000⟩,
  ⟨6, 3, 7, 5, 3, 8, -844026239666878714963819777122609809731249766400000⟩,
  ⟨6, 3, 8, 5, 4, 8, -308573745173492078884764681030534357359945318400000⟩,
  ⟨6, 3, 5, 6, 0, 8, -243154756673963018637558807137708707201633222656000000⟩,
  ⟨6, 3, 6, 6, 1, 8, 13536417950974754417853574706495175208591373107200000⟩,
  ⟨6, 3, 7, 6, 2, 8, -5973592798431772770613992844246562220630500966400000⟩,
  ⟨6, 3, 8, 6, 3, 8, 1638341682868651663819926339888914998240267468800000⟩,
  ⟨6, 3, 6, 7, 0, 8, 4016700525859301380816206106776495062233015910400000⟩,
  ⟨6, 3, 7, 7, 1, 8, 30904596626626932406649710285191390890879562547200000⟩,
  ⟨6, 3, 8, 7, 2, 8, -644403406750110793842390607993625043593802547200000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1006. -/
namespace LaughlinFock
def collectedFourData_10_1_47 : List CollectedFourTerm := [
  ⟨7, 0, 3, 0, 4, 6, 1217744959141844593939359486117734847282885427200000⟩,
  ⟨7, 0, 4, 0, 5, 6, -71736752481661037768421193516365164374461618585600000⟩,
  ⟨7, 0, 5, 0, 6, 6, -62568155316658527132189283533488353802402660352000000⟩,
  ⟨7, 0, 6, 0, 7, 6, -28718749767038947961433167392695704766092673024000000⟩,
  ⟨7, 0, 7, 0, 8, 6, -21060184294629437119896557750792230364208168960000000⟩,
  ⟨7, 0, 3, 1, 3, 6, -5845385916588405936141481138830530728533216460800000⟩,
  ⟨7, 0, 4, 1, 4, 6, -22075779096124348635600190295875943667319229644800000⟩,
  ⟨7, 0, 5, 1, 5, 6, 20508766094074845471587747331233648891060551680000000⟩,
  ⟨7, 0, 6, 1, 6, 6, 10583012003759802529066049114819906157699661824000000⟩,
  ⟨7, 0, 7, 1, 7, 6, 1666063315627876672395386597190337452362956800000000⟩,
  ⟨7, 0, 8, 1, 8, 6, 4815396755276591446690921112689123292525415628800000⟩,
  ⟨7, 0, 3, 2, 2, 6, 4561818520495682320759413641331303289216774963200000⟩,
  ⟨7, 0, 4, 2, 3, 6, -34661421334707458446796101295195538295409029939200000⟩,
  ⟨7, 0, 5, 2, 4, 6, -15406173831945685868124594568372089587622739968000000⟩,
  ⟨7, 0, 6, 2, 5, 6, 190134782898678556927606106660504244244709376000000⟩,
  ⟨7, 0, 7, 2, 6, 6, 1044950192514620089443715760728165014501851136000000⟩,
  ⟨7, 0, 8, 2, 7, 6, 2067622256699336399120431400998008765225212313600000⟩,
  ⟨7, 0, 3, 3, 1, 6, 102208457917987186926535115452520780857658572800000⟩,
  ⟨7, 0, 4, 3, 2, 6, 92470326154755202757511933280326407811522310963200000⟩,
  ⟨7, 0, 5, 3, 3, 6, 4600369259067662067653569796228513098496999424000000⟩,
  ⟨7, 0, 6, 3, 4, 6, -3078797869320422826311179406590659919393849344000000⟩,
  ⟨7, 0, 7, 3, 5, 6, 2506298820091752181602056265176755257584123904000000⟩,
  ⟨7, 0, 8, 3, 6, 6, -111029101744280873952970168571130202829094912000000⟩,
  ⟨7, 0, 3, 4, 0, 6, -19597792946877669996631701572281222460387151052800000⟩,
  ⟨7, 0, 4, 4, 1, 6, -1187151195523854068637610048474194958488698880000000⟩,
  ⟨7, 0, 5, 4, 2, 6, 9501072988804337976515390721271170142285332480000000⟩,
  ⟨7, 0, 6, 4, 3, 6, 3887320254686351045686540869393111086197112832000000⟩,
  ⟨7, 0, 7, 4, 4, 6, -1295768731426797189480657122823537986522578944000000⟩,
  ⟨7, 0, 8, 4, 5, 6, -1511231869629812627672852028066430153184929382400000⟩,
  ⟨7, 0, 4, 5, 0, 6, -381038279791455448542284757221599682859599973580800000⟩,
  ⟨7, 0, 5, 5, 1, 6, 3207707870531490101728075288319835999332990976000000⟩,
  ⟨7, 0, 6, 5, 2, 6, -8438348062261529511789078692350427554809643008000000⟩,
  ⟨7, 0, 7, 5, 3, 6, -1478062794557401071867889031057824552486699008000000⟩,
  ⟨7, 0, 8, 5, 4, 6, -756526149255099032740877225751989066071749427200000⟩,
  ⟨7, 0, 5, 6, 0, 6, -170325509927885787168890359878710527632372400128000000⟩,
  ⟨7, 0, 6, 6, 1, 6, 15803359978327504596102177843582601020473081856000000⟩,
  ⟨7, 0, 7, 6, 2, 6, -10460984327552196067260351396637083612645163008000000⟩,
  ⟨7, 0, 8, 6, 3, 6, 4016700525859301380816206106776495062233015910400000⟩,
  ⟨7, 0, 6, 7, 0, 6, 4689376803020546113404512211974803605046689792000000⟩,
  ⟨7, 0, 7, 7, 1, 6, 54120277673653902323120779895906273703267139584000000⟩,
  ⟨7, 0, 8, 7, 2, 6, -1579875266450270309260164378129874256655915417600000⟩
]

def collectedFourData_10_1_48 : List CollectedFourTerm := [
  ⟨7, 1, 2, 0, 3, 7, 153568030105498116088661307828197845221917274931200000⟩,
  ⟨7, 1, 3, 0, 4, 7, 56216165254195888552096514251328943293986347417600000⟩,
  ⟨7, 1, 4, 0, 5, 7, -1655833227653156693774873508286222275092689610342400000⟩,
  ⟨7, 1, 5, 0, 6, 7, -962801976042167868446248511000296563924661174272000000⟩,
  ⟨7, 1, 6, 0, 7, 7, -331444193358739846584329959762499138490936066048000000⟩,
  ⟨7, 1, 7, 0, 8, 7, -194445116229432795058392870286045023388708110336000000⟩,
  ⟨7, 1, 2, 1, 2, 7, -147304494696880013964735347636728251730939084800000000⟩,
  ⟨7, 1, 3, 1, 3, 7, -269847292895430292233976899380287785671649027686400000⟩,
  ⟨7, 1, 4, 1, 4, 7, -509554827743817550458538946087463184089679606579200000⟩,
  ⟨7, 1, 5, 1, 5, 7, 315589942225843606537875678992620607597162004480000000⟩,
  ⟨7, 1, 6, 1, 6, 7, 122138947737824472778296108750019142155814043648000000⟩,
  ⟨7, 1, 7, 1, 7, 7, 15382480538665999928179418212117328308343930880000000⟩,
  ⟨7, 1, 8, 1, 8, 7, 37049785853067622424865172716190256854527796838400000⟩,
  ⟨7, 1, 2, 2, 1, 7, -204125006439709334470244536375948630132705040793600000⟩,
  ⟨7, 1, 3, 2, 2, 7, 210592490556115917415671054642237028767561783705600000⟩,
  ⟨7, 1, 4, 2, 3, 7, -800057588031558346210904483283752782226728471756800000⟩,
  ⟨7, 1, 5, 2, 4, 7, -237070991362553248362159280259827281839152693248000000⟩,
  ⟨7, 1, 6, 2, 5, 7, 2194352827281493139568817399649202707210698752000000⟩,
  ⟨7, 1, 7, 2, 6, 7, 9647848223687570193593086904576654285102225817600000⟩,
  ⟨7, 1, 8, 2, 7, 7, 15908338550048866212544591135339097288002555084800000⟩,
  ⟨7, 1, 2, 3, 0, 7, 353495988376542330385624443625347028884918789734400000⟩,
  ⟨7, 1, 3, 3, 1, 7, 4718366943389514046026345339136188036418004582400000⟩,
  ⟨7, 1, 4, 3, 2, 7, 2134407166788198750690231017140093286485163035852800000⟩,
  ⟨7, 1, 5, 3, 3, 7, 70790717590082436591767252423156911602048958464000000⟩,
  ⟨7, 1, 6, 3, 4, 7, -35532524381778759136622058739582838053628018688000000⟩,
  ⟨7, 1, 7, 3, 5, 7, 23140232704549841092325046703950403491716294246400000⟩,
  ⟨7, 1, 8, 3, 6, 7, -854260749869982829249543517346032575857033216000000⟩,
  ⟨7, 1, 3, 4, 0, 7, -904715522448621950916584539673393111616551544422400000⟩,
  ⟨7, 1, 4, 4, 1, 7, -27401915026737371092687959183360899690287595520000000⟩,
  ⟨7, 1, 5, 4, 2, 7, 146202997384935781833839916116623066794326753280000000⟩,
  ⟨7, 1, 6, 4, 3, 7, 44863712264395433983433660436973395395859185664000000⟩,
  ⟨7, 1, 7, 4, 4, 7, -11963613331389488575702041495323446619018782310400000⟩,
  ⟨7, 1, 8, 4, 5, 7, -11627456674834161269505589907795083964871553843200000⟩,
  ⟨7, 1, 4, 5, 0, 7, -8795154824548076351310039453913324380111118742323200000⟩,
  ⟨7, 1, 5, 5, 1, 7, 49360372871524660931333647734210034626447015936000000⟩,
  ⟨7, 1, 6, 5, 2, 7, -97387298871434365825294503804381236338429526016000000⟩,
  ⟨7, 1, 7, 5, 3, 7, -13646703554982877232141144625195181828370910412800000⟩,
  ⟨7, 1, 8, 5, 4, 7, -5820731550610792444175360716024090724662876569600000⟩,
  ⟨7, 1, 5, 6, 0, 7, -2620977663461602639970515260982722680998758187008000000⟩,
  ⟨7, 1, 6, 6, 1, 7, 182387184082303807333754841552078391962041843712000000⟩,
  ⟨7, 1, 7, 6, 2, 7, -96584497314388400188674062653819961855760452812800000⟩,
  ⟨7, 1, 8, 6, 3, 7, 30904596626626932406649710285191390890879562547200000⟩,
  ⟨7, 1, 6, 7, 0, 7, 54120277673653902323120779895906273703267139584000000⟩,
  ⟨7, 1, 7, 7, 1, 7, 499683361522453090321362276957459720004545439334400000⟩,
  ⟨7, 1, 8, 7, 2, 7, -12155600726440770764325438601205826273145572556800000⟩
]

def collectedFourData_10_1_49 : List CollectedFourTerm := [
  ⟨7, 2, 1, 0, 2, 8, 23563777749833530675844192329001860227183673344000000⟩,
  ⟨7, 2, 2, 0, 3, 8, -22414734634600288298506910994836410911150204518400000⟩,
  ⟨7, 2, 3, 0, 4, 8, -4102645666165005586184404726923794815638935961600000⟩,
  ⟨7, 2, 4, 0, 5, 8, 80561608149608356044014789928465773174399277465600000⟩,
  ⟨7, 2, 5, 0, 6, 8, 35132557837442308897882491248078872836336254976000000⟩,
  ⟨7, 2, 6, 0, 7, 8, 9675495134256222929037688037805054803288732467200000⟩,
  ⟨7, 2, 7, 0, 8, 8, 4730189912447477015578845730757387651899195392000000⟩,
  ⟨7, 2, 1, 1, 1, 8, -23292135724548476982223805214617009717374667980800000⟩,
  ⟨7, 2, 2, 1, 2, 8, 21500511251242771775431311590861295817693593600000000⟩,
  ⟨7, 2, 3, 1, 3, 8, 19693407078156485408301854097151678196033676902400000⟩,
  ⟨7, 2, 4, 1, 4, 8, 24791480010109673260841995756289155050005908684800000⟩,
  ⟨7, 2, 5, 1, 5, 8, -11515848714542863036973614525659811183161507840000000⟩,
  ⟨7, 2, 6, 1, 6, 8, -3565471407312962418959075782794609821605901107200000⟩,
  ⟨7, 2, 7, 1, 7, 8, -374203557710150853647948737581424215179919360000000⟩,
  ⟨7, 2, 8, 1, 8, 8, -772539066324796817322429683032946405601076838400000⟩,
  ⟨7, 2, 1, 2, 0, 8, -44216839440538874404104891381816422272523776819200000⟩,
  ⟨7, 2, 2, 2, 1, 8, 29794012780452724997399689018526149912523125555200000⟩,
  ⟨7, 2, 3, 2, 2, 8, -15369002222051373652680999046829024800826562969600000⟩,
  ⟨7, 2, 4, 2, 3, 8, 38925372934731444251003138018887307198159074099200000⟩,
  ⟨7, 2, 5, 2, 4, 8, 8650699232943728914576337451619603301410013184000000⟩,
  ⟨7, 2, 6, 2, 5, 8, -64057390440458054456540817225009332740738252800000⟩,
  ⟨7, 2, 7, 2, 6, 8, -234699411481559209358826456793273709674836787200000⟩,
  ⟨7, 2, 8, 2, 7, 8, -331710770447434575121785474272560774302715084800000⟩,
  ⟨7, 2, 2, 3, 0, 8, -51596147768599023666800422442542386287246888140800000⟩,
  ⟨7, 2, 3, 3, 1, 8, -344345573984671222344818863751581775176296038400000⟩,
  ⟨7, 2, 4, 3, 2, 8, -103845768360510786758163795968032806261367190323200000⟩,
  ⟨7, 2, 5, 3, 3, 8, -2583146941919747394672491980767430523656077312000000⟩,
  ⟨7, 2, 6, 3, 4, 8, 1037262904743766183433336085188662931460666163200000⟩,
  ⟨7, 2, 7, 3, 5, 8, -562923345328950204046827340468506951167036620800000⟩,
  ⟨7, 2, 8, 3, 6, 8, 17812513268489924724358273536974919844233216000000⟩,
  ⟨7, 2, 3, 4, 0, 8, 66025976700874487875744329398236861744491685478400000⟩,
  ⟨7, 2, 4, 4, 1, 8, 1333191232103532544462721657253446839833722880000000⟩,
  ⟨7, 2, 5, 4, 2, 8, -5334934274593470701173761165992460193879818240000000⟩,
  ⟨7, 2, 6, 4, 3, 8, -1309658272543645520898331369526790448595179929600000⟩,
  ⟨7, 2, 7, 4, 4, 8, 291034119004500696289717946741762177440206028800000⟩,
  ⟨7, 2, 8, 4, 5, 8, 242448486988074430611548333754931067908993843200000⟩,
  ⟨7, 2, 4, 5, 0, 8, 427912548653600374404231835069429106367068425420800000⟩,
  ⟨7, 2, 5, 5, 1, 8, -1801155583326936961933291962123627044051877888000000⟩,
  ⟨7, 2, 6, 5, 2, 8, 2842923047829804576124827963196390070647416422400000⟩,
  ⟨7, 2, 7, 5, 3, 8, 331977993305702214158352995119372719370115481600000⟩,
  ⟨7, 2, 8, 5, 4, 8, 121370270135146550221995612806076508143196569600000⟩,
  ⟨7, 2, 5, 6, 0, 8, 95639240096632555337092875442789923672255627264000000⟩,
  ⟨7, 2, 6, 6, 1, 8, -5324233604023377098676282642470827782189141196800000⟩,
  ⟨7, 2, 7, 6, 2, 8, 2349573101935156456491863429842518559751248281600000⟩,
  ⟨7, 2, 8, 6, 3, 8, -644403406750110793842390607993625043593802547200000⟩,
  ⟨7, 2, 6, 7, 0, 8, -1579875266450270309260164378129874256655915417600000⟩,
  ⟨7, 2, 7, 7, 1, 8, -12155600726440770764325438601205826273145572556800000⟩,
  ⟨7, 2, 8, 7, 2, 8, 253461017914198072937026429688808092988132556800000⟩
]

def collectedFourData_10_1 : List (List CollectedFourTerm) := [
  collectedFourData_10_1_0,
  collectedFourData_10_1_1,
  collectedFourData_10_1_2,
  collectedFourData_10_1_3,
  collectedFourData_10_1_4,
  collectedFourData_10_1_5,
  collectedFourData_10_1_6,
  collectedFourData_10_1_7,
  collectedFourData_10_1_8,
  collectedFourData_10_1_9,
  collectedFourData_10_1_10,
  collectedFourData_10_1_11,
  collectedFourData_10_1_12,
  collectedFourData_10_1_13,
  collectedFourData_10_1_14,
  collectedFourData_10_1_15,
  collectedFourData_10_1_16,
  collectedFourData_10_1_17,
  collectedFourData_10_1_18,
  collectedFourData_10_1_19,
  collectedFourData_10_1_20,
  collectedFourData_10_1_21,
  collectedFourData_10_1_22,
  collectedFourData_10_1_23,
  collectedFourData_10_1_24,
  collectedFourData_10_1_25,
  collectedFourData_10_1_26,
  collectedFourData_10_1_27,
  collectedFourData_10_1_28,
  collectedFourData_10_1_29,
  collectedFourData_10_1_30,
  collectedFourData_10_1_31,
  collectedFourData_10_1_32,
  collectedFourData_10_1_33,
  collectedFourData_10_1_34,
  collectedFourData_10_1_35,
  collectedFourData_10_1_36,
  collectedFourData_10_1_37,
  collectedFourData_10_1_38,
  collectedFourData_10_1_39,
  collectedFourData_10_1_40,
  collectedFourData_10_1_41,
  collectedFourData_10_1_42,
  collectedFourData_10_1_43,
  collectedFourData_10_1_44,
  collectedFourData_10_1_45,
  collectedFourData_10_1_46,
  collectedFourData_10_1_47,
  collectedFourData_10_1_48,
  collectedFourData_10_1_49
]

def collectedFourData_10_2_0 : List CollectedFourTerm := [
  ⟨0, 2, 8, 2, 8, 0, -10360280526650034221496974501387895406964873625600000⟩,
  ⟨0, 2, 8, 3, 7, 0, -6346259885375588231536913599774296931427155968000000⟩,
  ⟨0, 2, 8, 4, 6, 0, 8094897445109575113615655379798753956628476723200000⟩,
  ⟨0, 2, 8, 5, 5, 0, 2705879587310989387891446164834364596249060966400000⟩,
  ⟨0, 2, 8, 6, 4, 0, -4030822154818050410845093447836384849092306534400000⟩,
  ⟨0, 2, 8, 7, 3, 0, -19305415248362306533418426668214241592757295513600000⟩
]

def collectedFourData_10_2_1 : List CollectedFourTerm := [
  ⟨0, 3, 7, 1, 8, 1, 22907903798457579660196277770108374178315055923200000⟩,
  ⟨0, 3, 7, 2, 7, 1, -1352508879285030363940207362529923410033639424000000⟩,
  ⟨0, 3, 8, 2, 8, 1, -21864487203824184209264182982834026260214893772800000⟩,
  ⟨0, 3, 7, 3, 6, 1, -1056067462920454296776439542620830497162605363200000⟩,
  ⟨0, 3, 8, 3, 7, 1, -13393239468661779258381002264152076487474806784000000⟩,
  ⟨0, 3, 7, 4, 5, 1, -3635945253508706422283668519252910982366756864000000⟩,
  ⟨0, 3, 8, 4, 6, 1, 17083589691378446438109520648786630182449027481600000⟩,
  ⟨0, 3, 7, 5, 4, 1, 2303959319293077366780963179399335596729040896000000⟩,
  ⟨0, 3, 8, 5, 5, 1, 5710527766083595081418582309107653368121340723200000⟩,
  ⟨0, 3, 7, 6, 3, 1, 6908464510682967075694846332303980127009216921600000⟩,
  ⟨0, 3, 8, 6, 4, 1, -8506705894517651792398791776545472237343552307200000⟩,
  ⟨0, 3, 7, 7, 2, 1, -12268132495297847970776523365050572415611332198400000⟩,
  ⟨0, 3, 8, 7, 3, 1, -40742430050667332915479222317224372342837005516800000⟩
]

def collectedFourData_10_2_2 : List CollectedFourTerm := [
  ⟨0, 4, 6, 0, 8, 2, -6816458612947291212272759929710082820606106009600000⟩,
  ⟨0, 4, 6, 1, 7, 2, 22797146151350977527157680182592132607213830144000000⟩,
  ⟨0, 4, 7, 1, 8, 2, 42856935179538209640966968958651560054286503116800000⟩,
  ⟨0, 4, 6, 2, 6, 2, -1573678291185118444917270723254497260929758003200000⟩,
  ⟨0, 4, 7, 2, 7, 2, -2530322541915477942843079749338673398862053376000000⟩,
  ⟨0, 4, 8, 2, 8, 2, -20452436832985744651948111380315536762154359193600000⟩,
  ⟨0, 4, 6, 3, 5, 2, 3833698172355380038356423746766390284508148531200000⟩,
  ⟨0, 4, 7, 3, 6, 2, -1975729215636425295638673423240250652745321676800000⟩,
  ⟨0, 4, 8, 3, 7, 2, -12528278466734227974553615178902043933181739008000000⟩,
  ⟨0, 4, 6, 4, 4, 2, -1771702606655818610071521634126747725050413056000000⟩,
  ⟨0, 4, 7, 4, 5, 2, -6802257920101104807938540653022299818804903936000000⟩,
  ⟨0, 4, 8, 4, 6, 2, 15980298819102992799792067528800151696445748019200000⟩,
  ⟨0, 4, 6, 5, 3, 2, -656284757606650889695694936200884003391773081600000⟩,
  ⟨0, 4, 7, 5, 4, 2, 4310330446292721697270272530563150447644770304000000⟩,
  ⟨0, 4, 8, 5, 5, 2, 5341730969039518997612674867237833876049389158400000⟩,
  ⟨0, 4, 6, 6, 2, 2, -47024753736468710097188565875612986307314817433600000⟩,
  ⟨0, 4, 7, 6, 3, 2, 12924605338373005099847469898281017759045674598400000⟩,
  ⟨0, 4, 8, 6, 4, 2, -7957326569908279651654604038420259299798705766400000⟩,
  ⟨0, 4, 6, 7, 1, 2, 93224415289957355207680338836067562387766299852800000⟩,
  ⟨0, 4, 7, 7, 2, 2, -22951666104009365387618019715310762208066640281600000⟩,
  ⟨0, 4, 8, 7, 3, 2, -38111206051421573978268677444328367324137101721600000⟩
]

def collectedFourData_10_2_3 : List CollectedFourTerm := [
  ⟨0, 5, 5, 0, 7, 3, 760543587660090356488100226921669037475758080000000⟩,
  ⟨0, 5, 6, 0, 8, 3, 46853259058863797197497723969135541008759521280000000⟩,
  ⟨0, 5, 5, 1, 6, 3, -125483792307616783448153558261864877178339983360000000⟩,
  ⟨0, 5, 6, 1, 7, 3, -156697290350039195922340435120574557249024819200000000⟩,
  ⟨0, 5, 7, 1, 8, 3, -147289611839044557798217270453788174783212421120000000⟩,
  ⟨0, 5, 5, 2, 5, 3, 21949854844140572880607229972824007493329879040000000⟩,
  ⟨0, 5, 6, 2, 6, 3, 10816754100458966467077784688238888203593973760000000⟩,
  ⟨0, 5, 7, 2, 7, 3, 8696147390498750460915093813808334769645158400000000⟩,
  ⟨0, 5, 8, 2, 8, 3, 46860272356126789648685983391987381968211804160000000⟩,
  ⟨0, 5, 5, 3, 4, 3, -29708212259109458993806929994533315305558507520000000⟩,
  ⟨0, 5, 6, 3, 5, 3, -26351110425827832690796129669356551376375644160000000⟩,
  ⟨0, 5, 7, 3, 6, 3, 6790135320014375893016800314703814769896325120000000⟩,
  ⟨0, 5, 8, 3, 7, 3, 28704576667251827346664996987791300503588044800000000⟩,
  ⟨0, 5, 5, 4, 3, 3, 2771075305512380725105156172883584572792504320000000⟩,
  ⟨0, 5, 6, 4, 4, 3, 12177883842386826448348679125621584513780940800000000⟩,
  ⟨0, 5, 7, 4, 5, 3, 23377824953733752983942284215108100719797862400000000⟩,
  ⟨0, 5, 8, 4, 6, 3, -36613786470066224257618891272624285903507947520000000⟩,
  ⟨0, 5, 5, 5, 2, 3, 215231387446322466677461574296143940659204587520000000⟩,
  ⟨0, 5, 6, 5, 3, 3, 4511005128986296501238641888598442623505530880000000⟩,
  ⟨0, 5, 7, 5, 4, 3, -14813632745152157354524917179688703107897753600000000⟩,
  ⟨0, 5, 8, 5, 5, 3, -12238882344750249627914161704642378988561367040000000⟩,
  ⟨0, 5, 5, 6, 1, 3, -274973065618596652508273941146704637347443507200000000⟩,
  ⟨0, 5, 6, 6, 2, 3, 323226926781177639383210877090443432483597844480000000⟩,
  ⟨0, 5, 7, 6, 3, 3, -44418950993273413729821001652391233186231746560000000⟩,
  ⟨0, 5, 8, 6, 4, 3, 18231690108005139543084667861435814451703971840000000⟩,
  ⟨0, 5, 5, 7, 0, 3, -1199688339056445036341049542717885286042052853760000000⟩,
  ⟨0, 5, 6, 7, 1, 3, -640782542403334916131861509151348409750299607040000000⟩,
  ⟨0, 5, 7, 7, 2, 3, 78879695371518663694514383061273607245597245440000000⟩,
  ⟨0, 5, 8, 7, 3, 3, 87319741406548471080550324897133367739243560960000000⟩
]

def collectedFourData_10_2_4 : List CollectedFourTerm := [
  ⟨0, 6, 4, 0, 6, 4, 61748649476041066677476536676065941184680296448000000⟩,
  ⟨0, 6, 5, 0, 7, 4, 798240391803679460621891199066224327789641728000000⟩,
  ⟨0, 6, 6, 0, 8, 4, 24587784628816028934384449878336710478789607424000000⟩,
  ⟨0, 6, 4, 1, 5, 4, -95686996353423751595247903121820139925319083622400000⟩,
  ⟨0, 6, 5, 1, 6, 4, -131703472571266803484470202381246337021405822976000000⟩,
  ⟨0, 6, 6, 1, 7, 4, -82232043286579609849658468658446619953709711360000000⟩,
  ⟨0, 6, 7, 1, 8, 4, -51530036923869887881703299755681789160313585664000000⟩,
  ⟨0, 6, 4, 2, 4, 4, 25512003468642075488908551472252196170742995353600000⟩,
  ⟨0, 6, 5, 2, 5, 4, 23037812710678506388023426987339021824362020864000000⟩,
  ⟨0, 6, 6, 2, 6, 4, 5676446538560114461148545931813450072413175808000000⟩,
  ⟨0, 6, 7, 2, 7, 4, 3042392403189336926731145620068527008886292480000000⟩,
  ⟨0, 6, 8, 2, 8, 4, 12295732543306752093925023120928316857792856064000000⟩,
  ⟨0, 6, 4, 3, 3, 4, -32540132914388526472770876592021331443011551232000000⟩,
  ⟨0, 6, 5, 3, 4, 4, -31180717815869659978901898833226856645087199232000000⟩,
  ⟨0, 6, 6, 3, 5, 4, -13828609597176557483832162747831599116087984128000000⟩,
  ⟨0, 6, 7, 3, 6, 4, 2375564164978408984747488104870870972538814464000000⟩,
  ⟨0, 6, 8, 3, 7, 4, 7531834104315144930107921373998262240852049920000000⟩,
  ⟨0, 6, 4, 4, 2, 4, 108485777193429676188589311842835132715071071846400000⟩,
  ⟨0, 6, 5, 4, 3, 4, 2908425333510674960184172401592977044759642112000000⟩,
  ⟨0, 6, 6, 4, 4, 4, 6390744020072593708213499957719027688291696640000000⟩,
  ⟨0, 6, 7, 4, 5, 4, 8178853674908846623551228207399039826950881280000000⟩,
  ⟨0, 6, 8, 4, 6, 4, -9607142750095791576871226295145568059741175808000000⟩,
  ⟨0, 6, 4, 5, 1, 4, -104593829688984557734121377876683942513433431244800000⟩,
  ⟨0, 6, 5, 5, 2, 4, 225899461689219301099118220870543508151029727232000000⟩,
  ⟨0, 6, 6, 5, 3, 4, 2367297916920814079475870009338314229079343104000000⟩,
  ⟨0, 6, 7, 5, 4, 4, -5182626478563272024673440796541203953662033920000000⟩,
  ⟨0, 6, 8, 5, 5, 4, -3211377492567489483752142382191709051385020416000000⟩,
  ⟨0, 6, 4, 6, 0, 4, -326335217833134928190318362464016013112194472345600000⟩,
  ⟨0, 6, 5, 6, 1, 4, -288602272369622751127947246288081713437889003520000000⟩,
  ⟨0, 6, 6, 6, 2, 4, 169623932711809328589063576900049124436668841984000000⟩,
  ⟨0, 6, 7, 6, 3, 4, -15540201078839327636141492937573897346882732032000000⟩,
  ⟨0, 6, 8, 6, 4, 4, 4783838721141641308661988775168032336129294336000000⟩,
  ⟨0, 6, 5, 7, 0, 4, -1259151619116299632924388922916719925922277359616000000⟩,
  ⟨0, 6, 6, 7, 1, 4, -336271658855665660139162627262224982866323832832000000⟩,
  ⟨0, 6, 7, 7, 2, 4, 27596471769372084100040775167160618754787770368000000⟩,
  ⟨0, 6, 8, 7, 3, 4, 22911949335805587751084334528308298276388470784000000⟩
]

def collectedFourData_10_2_5 : List CollectedFourTerm := [
  ⟨0, 7, 3, 0, 5, 5, 760543587660090356488100226921669037475758080000000⟩,
  ⟨0, 7, 4, 0, 6, 5, 798240391803679460621891199066224327789641728000000⟩,
  ⟨0, 7, 5, 0, 7, 5, 5159527605167504522934793555138195859963904000000⟩,
  ⟨0, 7, 6, 0, 8, 5, 105950834564708448856732443157429360879730688000000⟩,
  ⟨0, 7, 3, 1, 4, 5, -727542889806413753658319529141512104668508979200000⟩,
  ⟨0, 7, 4, 1, 5, 5, -1236969975988069252536245855298949908273718886400000⟩,
  ⟨0, 7, 5, 1, 6, 5, -851282031585037201855611771910289595373191168000000⟩,
  ⟨0, 7, 6, 1, 7, 5, -354344799488910858883515186241030498623160320000000⟩,
  ⟨0, 7, 7, 1, 8, 5, -166535451434156531324657132904668363464114176000000⟩,
  ⟨0, 7, 3, 2, 3, 5, 504680884280110899652792354646429576263945420800000⟩,
  ⟨0, 7, 4, 2, 4, 5, 329800114128930685497107714871006078309079449600000⟩,
  ⟨0, 7, 5, 2, 5, 5, 148907812563634629875815800707932009059581952000000⟩,
  ⟨0, 7, 6, 2, 6, 5, 24460286162485183488271762233920296002256896000000⟩,
  ⟨0, 7, 7, 2, 7, 5, 9832443804640187730224311923249787510456320000000⟩,
  ⟨0, 7, 8, 2, 8, 5, 31790008190189511288037840137485068125654220800000⟩,
  ⟨0, 7, 3, 3, 2, 5, -332793010982906456958308131886327928388897996800000⟩,
  ⟨0, 7, 4, 3, 3, 5, -420654519043428422516650714054659368395210752000000⟩,
  ⟨0, 7, 5, 3, 4, 5, -201540508312794412317994739666179084964069376000000⟩,
  ⟨0, 7, 6, 3, 5, 5, -59588643296203469943515912962099625104244736000000⟩,
  ⟨0, 7, 7, 3, 6, 5, 7677379529340609782348365322049305104613376000000⟩,
  ⟨0, 7, 8, 3, 7, 5, 19473184458104205458696452346581326678196224000000⟩,
  ⟨0, 7, 3, 4, 1, 5, 307279193278667007286334833065465989658417561600000⟩,
  ⟨0, 7, 4, 4, 2, 5, 1402423049359331147498463049040967195762779750400000⟩,
  ⟨0, 7, 5, 4, 3, 5, 18798974531856887338624128846105203982729216000000⟩,
  ⟨0, 7, 6, 4, 4, 5, 27538254163108621741278588834126736580935680000000⟩,
  ⟨0, 7, 7, 4, 5, 5, 26432526935254599898775755610782288073195520000000⟩,
  ⟨0, 7, 8, 4, 6, 5, -24838792291079655437195039757573275482954137600000⟩,
  ⟨0, 7, 3, 5, 0, 5, -369085275671963326255728201275713876474095206400000⟩,
  ⟨0, 7, 4, 5, 1, 5, -1352110860717326106768608889393263222469741772800000⟩,
  ⟨0, 7, 5, 5, 2, 5, 1460129705970403396874579179994955932422373376000000⟩,
  ⟨0, 7, 6, 5, 3, 5, 10200886080119112068537707589223474001870848000000⟩,
  ⟨0, 7, 7, 5, 4, 5, -16749280453597812720030148336973329496801280000000⟩,
  ⟨0, 7, 8, 5, 5, 5, -8302857632185878308021464172569479133475635200000⟩,
  ⟨0, 7, 4, 6, 0, 5, -4218617805455555629578227747977761955608369561600000⟩,
  ⟨0, 7, 5, 6, 1, 5, -1865417243345109067357990031284186176144015360000000⟩,
  ⟨0, 7, 6, 6, 2, 5, 730923810512876636762400409455850344476049408000000⟩,
  ⟨0, 7, 7, 6, 3, 5, -50223026346081575830142019268876676930469888000000⟩,
  ⟨0, 7, 8, 6, 4, 5, 12368378345088769619507077074591009492644659200000⟩,
  ⟨0, 7, 5, 7, 0, 5, -8138685544641918331715189348369213491865714688000000⟩,
  ⟨0, 7, 6, 7, 1, 5, -1449022896290608608864759275565619609583222784000000⟩,
  ⟨0, 7, 7, 7, 2, 5, 89186640616852757590972851594397159325171712000000⟩,
  ⟨0, 7, 8, 7, 3, 5, 59237711496494729492095846053938958533709004800000⟩
]

def collectedFourData_10_2_6 : List CollectedFourTerm := [
  ⟨0, 8, 2, 0, 4, 6, -6816458612947291212272759929710082820606106009600000⟩,
  ⟨0, 8, 3, 0, 5, 6, 46853259058863797197497723969135541008759521280000000⟩,
  ⟨0, 8, 4, 0, 6, 6, 24587784628816028934384449878336710478789607424000000⟩,
  ⟨0, 8, 5, 0, 7, 6, 105950834564708448856732443157429360879730688000000⟩,
  ⟨0, 8, 6, 0, 8, 6, 1631774292725260910694796536564411664592535552000000⟩,
  ⟨0, 8, 2, 1, 3, 6, 4069735820059318987939931031955863263963932262400000⟩,
  ⟨0, 8, 3, 1, 4, 6, -44820252311126100197362902962397712221740413747200000⟩,
  ⟨0, 8, 4, 1, 5, 6, -38101744379513354140207610143981288021537534771200000⟩,
  ⟨0, 8, 5, 1, 6, 6, -17481065825879427863254359188040532805912887296000000⟩,
  ⟨0, 8, 6, 1, 7, 6, -5457349505007959982088963864464981446916833280000000⟩,
  ⟨0, 8, 7, 1, 8, 6, -2051882042036659420313315301945272124732289843200000⟩,
  ⟨0, 8, 2, 2, 2, 6, 993607991822548920139024622803169771467151769600000⟩,
  ⟨0, 8, 3, 2, 3, 6, 31090846858603160591059278805045506630109416652800000⟩,
  ⟨0, 8, 4, 2, 4, 6, 10158661801663687195245557643468306339391655116800000⟩,
  ⟨0, 8, 5, 2, 5, 6, 3057820060604185539891344769536690896811065344000000⟩,
  ⟨0, 8, 6, 2, 6, 6, 376718751830782990000043621395273888441565184000000⟩,
  ⟨0, 8, 7, 2, 7, 6, 121145466015399410989930446951644138594893824000000⟩,
  ⟨0, 8, 8, 2, 8, 6, 326403709439998951025766875840538214346312908800000⟩,
  ⟨0, 8, 2, 3, 1, 6, 5694431390258088605398675829075379933161717760000000⟩,
  ⟨0, 8, 3, 3, 2, 6, -20501700901237690735234624362437352111796440268800000⟩,
  ⟨0, 8, 4, 3, 3, 6, -12957202897246740618597110355507745517696188416000000⟩,
  ⟨0, 8, 5, 3, 4, 6, -4138631806708375803013363247262042543957737472000000⟩,
  ⟨0, 8, 6, 3, 5, 6, -917739031208242234225443007991404513978220544000000⟩,
  ⟨0, 8, 7, 3, 6, 6, 94592935320934861551168209058788456365503283200000⟩,
  ⟨0, 8, 8, 3, 7, 6, 199940799124929620426757268322946388133412864000000⟩,
  ⟨0, 8, 2, 4, 0, 6, -21807212599951052825734733367044666910485721907200000⟩,
  ⟨0, 8, 3, 4, 1, 6, 18929923122984146444146871436095414619923388825600000⟩,
  ⟨0, 8, 4, 4, 2, 6, 43198109554715870092484183856652589554774258483200000⟩,
  ⟨0, 8, 5, 4, 3, 6, 386036705882935892519398054672560735966461952000000⟩,
  ⟨0, 8, 6, 4, 4, 6, 424123277504253009379722347968894574757150720000000⟩,
  ⟨0, 8, 7, 4, 5, 6, 325674965162254240575675766407729498254475264000000⟩,
  ⟨0, 8, 8, 4, 6, 6, -255032143852043412508852775484354729034226073600000⟩,
  ⟨0, 8, 3, 5, 0, 6, -22737484499835593683283523698955546754896258662400000⟩,
  ⟨0, 8, 4, 5, 1, 6, -41648369312006841935982796921250035600418301542400000⟩,
  ⟨0, 8, 5, 5, 2, 6, 29983745171814850222644504665010286365845225472000000⟩,
  ⟨0, 8, 6, 5, 3, 6, 157106300643542531790108085296735553629192192000000⟩,
  ⟨0, 8, 7, 5, 4, 6, -206367758238917400407131699492576795343978496000000⟩,
  ⟨0, 8, 8, 5, 5, 6, -85249538593513692201896567340735172304909107200000⟩,
  ⟨0, 8, 4, 6, 0, 6, -129943895469198926588407086724608849819103710412800000⟩,
  ⟨0, 8, 5, 6, 1, 6, -38306319661099216401486708513809988117772369920000000⟩,
  ⟨0, 8, 6, 6, 2, 6, 11257133450961825648597525858412083426657042432000000⟩,
  ⟨0, 8, 7, 6, 3, 6, -618797529107504087616605017977777695135209881600000⟩,
  ⟨0, 8, 8, 6, 4, 6, 126992246980300742460627894041115686056702771200000⟩,
  ⟨0, 8, 5, 7, 0, 6, -167127805431432574908111227536980467271635828736000000⟩,
  ⟨0, 8, 6, 7, 1, 6, -22316750230912382888265690207052941062660161536000000⟩,
  ⟨0, 8, 7, 7, 2, 6, 1098867926890934584738459643681700086502811238400000⟩,
  ⟨0, 8, 8, 7, 3, 6, 608222830755964207026707224643987583452105932800000⟩
]

def collectedFourData_10_2_7 : List CollectedFourTerm := [
  ⟨1, 1, 8, 2, 8, 0, 76331577568473640276555581865597789251432559411200000⟩,
  ⟨1, 1, 8, 3, 7, 0, 46757423938874280297367366027109775636468596736000000⟩,
  ⟨1, 1, 8, 4, 6, 0, -59640884303353467777668271020347856812859876966400000⟩,
  ⟨1, 1, 8, 5, 5, 0, -19936145269279077423212471366267363633883040972800000⟩,
  ⟨1, 1, 8, 6, 4, 0, 29697942365920005662230663698561285503266376908800000⟩,
  ⟨1, 1, 8, 7, 3, 0, 142236766439996148285686545693173527430820999987200000⟩
]

def collectedFourData_10_2_8 : List CollectedFourTerm := [
  ⟨1, 2, 7, 1, 8, 1, 6722736166706000464345515570901377811224723456000000⟩,
  ⟨1, 2, 7, 2, 7, 1, -396918043595620835920946408205632418003025920000000⟩,
  ⟨1, 2, 8, 2, 8, 1, -6416526810345972217275350222259198067394740224000000⟩,
  ⟨1, 2, 7, 3, 6, 1, -309921981073397740069563742567598782892998656000000⟩,
  ⟨1, 2, 8, 3, 7, 1, -3930486881623331386512110997856145659102494720000000⟩,
  ⟨1, 2, 7, 4, 5, 1, -1067033495119348819004506475999608320420741120000000⟩,
  ⟨1, 2, 8, 4, 6, 1, 5013486492951336126059407185322366358758883328000000⟩,
  ⟨1, 2, 7, 5, 4, 1, 676138278678898527149512879584558819500359680000000⟩,
  ⟨1, 2, 8, 5, 5, 1, 1675857026543558474870545192914215053301907456000000⟩,
  ⟨1, 2, 7, 6, 3, 1, 2027413098596143854632254671623864221358358528000000⟩,
  ⟨1, 2, 8, 6, 4, 1, -2496445762988384204048577509245842701131186176000000⟩,
  ⟨1, 2, 7, 7, 2, 1, -3600304015142282764251616042859169514700931072000000⟩,
  ⟨1, 2, 8, 7, 3, 1, -11956598492418706886204199461846942175140511744000000⟩
]

def collectedFourData_10_2_9 : List CollectedFourTerm := [
  ⟨1, 3, 6, 0, 8, 2, 4069735820059318987939931031955863263963932262400000⟩,
  ⟨1, 3, 6, 1, 7, 2, -13610933118710029796586577798757045127333543936000000⟩,
  ⟨1, 3, 7, 1, 8, 2, -25587539533627870505682831298963572599783895859200000⟩,
  ⟨1, 3, 6, 2, 6, 2, 939557514325854049952373660420197306136841420800000⟩,
  ⟨1, 3, 7, 2, 7, 2, 1510717642380644241474022446158738614275538944000000⟩,
  ⟨1, 3, 8, 2, 8, 2, 12211035012902863386852010440204547682654905958400000⟩,
  ⟨1, 3, 6, 3, 5, 2, -2288892174258299092999556917005705122249755852800000⟩,
  ⟨1, 3, 7, 3, 6, 2, 1179600202418985577812385559759283212369736499200000⟩,
  ⟨1, 3, 8, 3, 7, 2, 7479952059402372551700281757022980806962839552000000⟩,
  ⟨1, 3, 6, 4, 4, 2, 1057787037260693434330640643814954083878436864000000⟩,
  ⟨1, 3, 7, 4, 5, 2, 4061257360550152182973637941454518568651587584000000⟩,
  ⟨1, 3, 8, 4, 6, 2, -9540965215548353822258005074632795989857848524800000⟩,
  ⟨1, 3, 6, 5, 3, 2, 391831849623142093217844659579507710676592230400000⟩,
  ⟨1, 3, 7, 5, 4, 2, -2573463320124966519516823648802242618485374976000000⟩,
  ⟨1, 3, 8, 5, 5, 2, -3189256342659820000385678157413066238601042329600000⟩,
  ⟨1, 3, 6, 6, 2, 2, 28075916774036878925151360066678973067939964518400000⟩,
  ⟨1, 3, 7, 6, 3, 2, -7716577227623408635688711726181047231441377689600000⟩,
  ⟨1, 3, 8, 6, 4, 2, 4750885879649350085050846642434546211552336281600000⟩,
  ⟨1, 3, 6, 7, 1, 2, -55659215987754848930968708224401822440439886643200000⟩,
  ⟨1, 3, 7, 7, 2, 2, 13703188558367985501504820438381224508365629030400000⟩,
  ⟨1, 3, 8, 7, 3, 2, 22754123397526040546116063946773320381980108390400000⟩
]

def collectedFourData_10_2_10 : List CollectedFourTerm := [
  ⟨1, 4, 5, 0, 7, 3, -727542889806413753658319529141512104668508979200000⟩,
  ⟨1, 4, 6, 0, 8, 3, -44820252311126100197362902962397712221740413747200000⟩,
  ⟨1, 4, 5, 1, 6, 3, 120038933153366797286749209096070977377068803686400000⟩,
  ⟨1, 4, 6, 1, 7, 3, 149898048311537379141698132535878101712353886208000000⟩,
  ⟨1, 4, 7, 1, 8, 3, 140898577773212696759294309381425259375932263628800000⟩,
  ⟨1, 4, 5, 2, 5, 3, -20997430105576764042935187551482748648732334489600000⟩,
  ⟨1, 4, 6, 2, 6, 3, -10347405019593005519422156104161851649558996582400000⟩,
  ⟨1, 4, 7, 2, 7, 3, -8318813418874829596767434695387299373400457216000000⟩,
  ⟨1, 4, 8, 2, 8, 3, -44826961294859021220113085459431761404282431078400000⟩,
  ⟨1, 4, 5, 3, 4, 3, 28419145133381579199019641778460678757448207564800000⟩,
  ⟨1, 4, 6, 3, 5, 3, 25207711089641115446834896366067442301427672678400000⟩,
  ⟨1, 4, 7, 3, 6, 3, -6495504995445102427751497020744193470500752588800000⟩,
  ⟨1, 4, 8, 3, 7, 3, -27459058228883194883349148483001095505578033152000000⟩,
  ⟨1, 4, 5, 4, 3, 3, -2650835755313360124464287093961175662735445196800000⟩,
  ⟨1, 4, 6, 4, 4, 3, -11649474068508896518966309307256628030778376192000000⟩,
  ⟨1, 4, 7, 4, 5, 3, -22363439256067325126521447233241449338215858176000000⟩,
  ⟨1, 4, 8, 4, 6, 3, 35025080018283339026284288262689024518394793164800000⟩,
  ⟨1, 4, 5, 5, 2, 3, -205892296168732025231884312642733794948394306764800000⟩,
  ⟨1, 4, 6, 5, 3, 3, -4315268395821444646564240933186537302850220851200000⟩,
  ⟨1, 4, 7, 5, 4, 3, 14170855360305435758151073455829415287968497664000000⟩,
  ⟨1, 4, 8, 5, 5, 3, 11707825788782925798778885031416733675856435609600000⟩,
  ⟨1, 4, 5, 6, 1, 3, 263041727029184897099245994961599285562156515328000000⟩,
  ⟨1, 4, 6, 6, 2, 3, -309201808008306772052428530988323766235378692915200000⟩,
  ⟨1, 4, 7, 6, 3, 3, 42491571150106003914965420826434401806030628454400000⟩,
  ⟨1, 4, 8, 6, 4, 3, -17440600016157515799977228149422082115440843161600000⟩,
  ⟨1, 4, 5, 7, 0, 3, 1147632739564000068745151178184047317822946567782400000⟩,
  ⟨1, 4, 6, 7, 1, 3, 612978388355014846146587708607452993207286733209600000⟩,
  ⟨1, 4, 7, 7, 2, 3, -75457031587376765631253923054112633358758025625600000⟩,
  ⟨1, 4, 8, 7, 3, 3, -83530856128211789135995365520355905796236011110400000⟩
]

def collectedFourData_10_2_11 : List CollectedFourTerm := [
  ⟨1, 5, 4, 0, 6, 4, -95686996353423751595247903121820139925319083622400000⟩,
  ⟨1, 5, 5, 0, 7, 4, -1236969975988069252536245855298949908273718886400000⟩,
  ⟨1, 5, 6, 0, 8, 4, -38101744379513354140207610143981288021537534771200000⟩,
  ⟨1, 5, 4, 1, 5, 4, 148278567204821647801818626170190705614931487621120000⟩,
  ⟨1, 5, 5, 1, 6, 4, 204090450667262629177192617223989832697290476748800000⟩,
  ⟨1, 5, 6, 1, 7, 4, 127428491033647269340142401444702529421016301568000000⟩,
  ⟨1, 5, 7, 1, 8, 4, 79852021008804386608510730793680044413936677683200000⟩,
  ⟨1, 5, 4, 2, 4, 4, -39533933188606485208721375634941397948245401927680000⟩,
  ⟨1, 5, 5, 2, 5, 4, -35699875536433951197479467000016652797480219443200000⟩,
  ⟨1, 5, 6, 2, 6, 4, -8796340063216402403231205445819792722137343590400000⟩,
  ⟨1, 5, 7, 2, 7, 4, -4714554783949046698176810564066084600491802624000000⟩,
  ⟨1, 5, 8, 2, 8, 4, -19053723846876583716130308678580165288932881203200000⟩,
  ⟨1, 5, 4, 3, 3, 4, 50424869303856519299344032331987128728726116761600000⟩,
  ⟨1, 5, 5, 3, 4, 4, 48318291286709191559509613102674227021418699161600000⟩,
  ⟨1, 5, 6, 3, 5, 4, 21429102131397584323801400661439142650054076006400000⟩,
  ⟨1, 5, 7, 3, 6, 4, -3681223824657272158025853981358248488005219123200000⟩,
  ⟨1, 5, 8, 3, 7, 4, -11671487370000412865373903394800271728360554496000000⟩,
  ⟨1, 5, 4, 4, 2, 4, -168111825194392745913044085224644762110565621432320000⟩,
  ⟨1, 5, 5, 4, 3, 4, -4506956615947091871627544672152804197700049305600000⟩,
  ⟨1, 5, 6, 4, 4, 4, -9903230352942727219162064125784200613128568832000000⟩,
  ⟨1, 5, 7, 4, 5, 4, -12674122404407366194720119017534420432468312064000000⟩,
  ⟨1, 5, 8, 4, 6, 4, 14887428973680215616813785868895130218303743590400000⟩,
  ⟨1, 5, 4, 5, 1, 4, 162080782089392464418257344545542629249761138442240000⟩,
  ⟨1, 5, 5, 5, 2, 4, -350058521932269053542642013544371450381432625561600000⟩,
  ⟨1, 5, 6, 5, 3, 4, -3668414274092923652908498491053993113645429555200000⟩,
  ⟨1, 5, 7, 5, 4, 4, 8031106188773536283177664556598627517591453696000000⟩,
  ⟨1, 5, 8, 5, 5, 4, 4976417606347846276202294119350585689123900620800000⟩,
  ⟨1, 5, 4, 6, 0, 4, 505695866448202418599527182874998328177512970977280000⟩,
  ⟨1, 5, 5, 6, 1, 4, 447224106407977604014293236118454210661424562176000000⟩,
  ⟨1, 5, 6, 6, 2, 4, -262852787365753925402813763855125028768956232499200000⟩,
  ⟨1, 5, 7, 6, 3, 4, 24081420024244185788429628842771967447748155801600000⟩,
  ⟨1, 5, 8, 6, 4, 4, -7413136354388745211560310158780297358613466316800000⟩,
  ⟨1, 5, 5, 7, 0, 4, 1951207636266406591150729601785807371094952037580800000⟩,
  ⟨1, 5, 6, 7, 1, 4, 521093582899601427469058123768157734577500690841600000⟩,
  ⟨1, 5, 7, 7, 2, 4, -42764068784821756950837403284280041006996809318400000⟩,
  ⟨1, 5, 8, 7, 3, 4, -35504835023083654606593007876176910101039493939200000⟩
]

def collectedFourData_10_2_12 : List CollectedFourTerm := [
  ⟨1, 6, 3, 0, 5, 5, -125483792307616783448153558261864877178339983360000000⟩,
  ⟨1, 6, 4, 0, 6, 5, -131703472571266803484470202381246337021405822976000000⟩,
  ⟨1, 6, 5, 0, 7, 5, -851282031585037201855611771910289595373191168000000⟩,
  ⟨1, 6, 6, 0, 8, 5, -17481065825879427863254359188040532805912887296000000⟩,
  ⟨1, 6, 3, 1, 4, 5, 120038933153366797286749209096070977377068803686400000⟩,
  ⟨1, 6, 4, 1, 5, 5, 204090450667262629177192617223989832697290476748800000⟩,
  ⟨1, 6, 5, 1, 6, 5, 140454931682843751318450224736003167413868691456000000⟩,
  ⟨1, 6, 6, 1, 7, 5, 58464143207296529135764506688442472869595709440000000⟩,
  ⟨1, 6, 7, 1, 8, 5, 27477057644930952519305946948574317521972232192000000⟩,
  ⟨1, 6, 3, 2, 3, 5, -83268431017176044960390771467349769859360201113600000⟩,
  ⟨1, 6, 4, 2, 4, 5, -54414460519886796399786550848020653275845178163200000⟩,
  ⟨1, 6, 5, 2, 5, 5, -24568633971663663023797967275685053530409795584000000⟩,
  ⟨1, 6, 6, 2, 6, 5, -4035757474520916484163547526817174643573522432000000⟩,
  ⟨1, 6, 7, 2, 7, 5, -1622276955951682114994920670932643184314941440000000⟩,
  ⟨1, 6, 8, 2, 8, 5, -5245104751284864985934451808098142442323810713600000⟩,
  ⟨1, 6, 3, 3, 2, 5, 54908265284420902739482888994890677454724766105600000⟩,
  ⟨1, 6, 4, 3, 3, 5, 69404732558862016375527649826926855446734045184000000⟩,
  ⟨1, 6, 5, 3, 4, 5, 33252620490171161961609666631927809530073710592000000⟩,
  ⟨1, 6, 6, 3, 5, 5, 9831663905389910099535004262457769505127923712000000⟩,
  ⟨1, 6, 7, 3, 6, 5, -1266708067699983105943131892364927337435758592000000⟩,
  ⟨1, 6, 8, 3, 7, 5, -3212924379030808657486144242230785538531524608000000⟩,
  ⟨1, 6, 3, 4, 1, 5, -50698683277920498615825062644925273980773020467200000⟩,
  ⟨1, 6, 4, 4, 2, 5, -231388924327992937112523559880877537249383468236800000⟩,
  ⟨1, 6, 5, 4, 3, 5, -3101684971152501170007341620083981060377935872000000⟩,
  ⟨1, 6, 6, 4, 4, 5, -4543598318341615439496998495040463616669122560000000⟩,
  ⟨1, 6, 7, 4, 5, 5, -4361161903045819357736641831321920675344547840000000⟩,
  ⟨1, 6, 8, 4, 6, 5, 4098208049607398392544224081045669356051313459200000⟩,
  ⟨1, 6, 3, 5, 0, 5, 60896207433306688720210886016270916878838058188800000⟩,
  ⟨1, 6, 4, 5, 1, 5, 223087803481627156352270466424108990951144921497600000⟩,
  ⟨1, 6, 5, 5, 2, 5, -240910075029203085331669775871746459515949678592000000⟩,
  ⟨1, 6, 6, 5, 3, 5, -1683067073340991058656210891341024014962262016000000⟩,
  ⟨1, 6, 7, 5, 4, 5, 2763501348039284395727092170177971503245557760000000⟩,
  ⟨1, 6, 8, 5, 5, 5, 1369907102737375588942484741241419978252904038400000⟩,
  ⟨1, 6, 4, 6, 0, 5, 696039213417955327868690350268388120480424604467200000⟩,
  ⟨1, 6, 5, 6, 1, 5, 307779374816820992232872525313284123906927493120000000⟩,
  ⟨1, 6, 6, 6, 2, 5, -120596758843599189021115974011112599530594369536000000⟩,
  ⟨1, 6, 7, 6, 3, 5, 8286409759184370223568490569857965385838493696000000⟩,
  ⟨1, 6, 8, 6, 4, 5, -2040686483482381507601636331295581041712326246400000⟩,
  ⟨1, 6, 5, 7, 0, 5, 1342819981801341443261784786564243562275375415296000000⟩,
  ⟨1, 6, 6, 7, 1, 5, 239077537589307537888970503651028721467945648128000000⟩,
  ⟨1, 6, 7, 7, 2, 5, -14715103866973915439726816842948092558525333504000000⟩,
  ⟨1, 6, 8, 7, 3, 5, -9773762880671165280539595891239479459050002841600000⟩
]

def collectedFourData_10_2_13 : List CollectedFourTerm := [
  ⟨1, 7, 2, 0, 4, 6, 22797146151350977527157680182592132607213830144000000⟩,
  ⟨1, 7, 3, 0, 5, 6, -156697290350039195922340435120574557249024819200000000⟩,
  ⟨1, 7, 4, 0, 6, 6, -82232043286579609849658468658446619953709711360000000⟩,
  ⟨1, 7, 5, 0, 7, 6, -354344799488910858883515186241030498623160320000000⟩,
  ⟨1, 7, 6, 0, 8, 6, -5457349505007959982088963864464981446916833280000000⟩,
  ⟨1, 7, 2, 1, 3, 6, -13610933118710029796586577798757045127333543936000000⟩,
  ⟨1, 7, 3, 1, 4, 6, 149898048311537379141698132535878101712353886208000000⟩,
  ⟨1, 7, 4, 1, 5, 6, 127428491033647269340142401444702529421016301568000000⟩,
  ⟨1, 7, 5, 1, 6, 6, 58464143207296529135764506688442472869595709440000000⟩,
  ⟨1, 7, 6, 1, 7, 6, 18251705369172084846062301553755185594184499200000000⟩,
  ⟨1, 7, 7, 1, 8, 6, 6862369076633594480945925994094591628854427648000000⟩,
  ⟨1, 7, 2, 2, 2, 6, -3323049092340194122866585264497836479473516544000000⟩,
  ⟨1, 7, 3, 2, 3, 6, -103981058207934341605795413081189160639153569792000000⟩,
  ⟨1, 7, 4, 2, 4, 6, -33974899716223699122037940679271609058828746752000000⟩,
  ⟨1, 7, 5, 2, 5, 6, -10226655039571287107032612601067151774879580160000000⟩,
  ⟨1, 7, 6, 2, 6, 6, -1259908250176782331512063777255160320633077760000000⟩,
  ⟨1, 7, 7, 2, 7, 6, -405162130535177200788896602993613230949007360000000⟩,
  ⟨1, 7, 8, 2, 8, 6, -1091633279238732683758000683178330391033413632000000⟩,
  ⟨1, 7, 2, 3, 1, 6, -19044608355133014465533932237506439163569766400000000⟩,
  ⟨1, 7, 3, 3, 2, 6, 68566435789553548702074424103574499701169324032000000⟩,
  ⟨1, 7, 4, 3, 3, 6, 43334415263694108622576711068709323767273226240000000⟩,
  ⟨1, 7, 5, 3, 4, 6, 13841350695646063770817668012718537861842862080000000⟩,
  ⟨1, 7, 6, 3, 5, 6, 3069310915130371636966654343978203675266908160000000⟩,
  ⟨1, 7, 7, 3, 6, 6, -316359138057502210189375625949167094488629248000000⟩,
  ⟨1, 7, 8, 3, 7, 6, -668687346037902789081416233850869289802792960000000⟩,
  ⟨1, 7, 2, 4, 0, 6, 72932623965527607973773887452834978327437508608000000⟩,
  ⟨1, 7, 3, 4, 1, 6, -63309740229159210037588856827844394934163472384000000⟩,
  ⟨1, 7, 4, 4, 2, 6, -144472910773696467455277399364561274253499957248000000⟩,
  ⟨1, 7, 5, 4, 3, 6, -1291071464452744277068754683637619913685729280000000⟩,
  ⟨1, 7, 6, 4, 4, 6, -1418449211308841384208710419316467460525260800000000⟩,
  ⟨1, 7, 7, 4, 5, 6, -1089196047422324186303973771685054536178728960000000⟩,
  ⟨1, 7, 8, 4, 6, 6, 852936310013558294755742008229915173117231104000000⟩,
  ⟨1, 7, 3, 5, 0, 6, 76043850141225480056803974801691476847478439936000000⟩,
  ⟨1, 7, 4, 5, 1, 6, 139289918135471959495836349328113928022981083136000000⟩,
  ⟨1, 7, 5, 5, 2, 6, -100278437772422358880285206821395210537355182080000000⟩,
  ⟨1, 7, 6, 5, 3, 6, -525430505844489902942273301016807983682682880000000⟩,
  ⟨1, 7, 7, 5, 4, 6, 690181839667196032112159138598430472342077440000000⟩,
  ⟨1, 7, 8, 5, 5, 6, 285110832619177693868646190066524438405316608000000⟩,
  ⟨1, 7, 4, 6, 0, 6, 434587832875632341679286990215004212774611976192000000⟩,
  ⟨1, 7, 5, 6, 1, 6, 128112678066545600680933938961819560930233548800000000⟩,
  ⟨1, 7, 6, 6, 2, 6, -37648657623973627256479069565832094412156436480000000⟩,
  ⟨1, 7, 7, 6, 3, 6, 2069522975224101657727005074677878559787188224000000⟩,
  ⟨1, 7, 8, 6, 4, 6, -424716260874737911045076930525083128003821568000000⟩,
  ⟨1, 7, 5, 7, 0, 6, 558946693982425493528928941171227417549775831040000000⟩,
  ⟨1, 7, 6, 7, 1, 6, 74636735220685081627899993449260129719460823040000000⟩,
  ⟨1, 7, 7, 7, 2, 6, -3675083229109955118966013434820885153711128576000000⟩,
  ⟨1, 7, 8, 7, 3, 6, -2034156671764324599124242235876437396125908992000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1007
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1007. -/
namespace LaughlinFock
def collectedFourData_10_2_14 : List CollectedFourTerm := [
  ⟨1, 8, 1, 0, 3, 7, 22907903798457579660196277770108374178315055923200000⟩,
  ⟨1, 8, 2, 0, 4, 7, 42856935179538209640966968958651560054286503116800000⟩,
  ⟨1, 8, 3, 0, 5, 7, -147289611839044557798217270453788174783212421120000000⟩,
  ⟨1, 8, 4, 0, 6, 7, -51530036923869887881703299755681789160313585664000000⟩,
  ⟨1, 8, 5, 0, 7, 7, -166535451434156531324657132904668363464114176000000⟩,
  ⟨1, 8, 6, 0, 8, 7, -2051882042036659420313315301945272124732289843200000⟩,
  ⟨1, 8, 1, 1, 2, 7, 6722736166706000464345515570901377811224723456000000⟩,
  ⟨1, 8, 2, 1, 3, 7, -25587539533627870505682831298963572599783895859200000⟩,
  ⟨1, 8, 3, 1, 4, 7, 140898577773212696759294309381425259375932263628800000⟩,
  ⟨1, 8, 4, 1, 5, 7, 79852021008804386608510730793680044413936677683200000⟩,
  ⟨1, 8, 5, 1, 6, 7, 27477057644930952519305946948574317521972232192000000⟩,
  ⟨1, 8, 6, 1, 7, 7, 6862369076633594480945925994094591628854427648000000⟩,
  ⟨1, 8, 7, 1, 8, 7, 2150123709511806755452394965009594746475747737600000⟩,
  ⟨1, 8, 1, 2, 1, 7, 24626943702468280027813728072457544427100333670400000⟩,
  ⟨1, 8, 2, 2, 2, 7, -6247084551870862623699176998033912402423893196800000⟩,
  ⟨1, 8, 3, 2, 3, 7, -97738318689796771897891543629316395426047537971200000⟩,
  ⟨1, 8, 4, 2, 4, 7, -21290092850550694559025664356067210834136059084800000⟩,
  ⟨1, 8, 5, 2, 5, 7, -4806337262837956159182421160661241013194457088000000⟩,
  ⟨1, 8, 6, 2, 6, 7, -473706716196070312065453105742567880926848614400000⟩,
  ⟨1, 8, 7, 2, 7, 7, -126945766590472135122257884885158874193068032000000⟩,
  ⟨1, 8, 8, 2, 8, 7, -293169882991746059810353849618780609982968627200000⟩,
  ⟨1, 8, 1, 3, 0, 7, 21613572924435090276243175024472511573847651123200000⟩,
  ⟨1, 8, 2, 3, 1, 7, -35802443883848115242838279678321098154395566080000000⟩,
  ⟨1, 8, 3, 3, 2, 7, 64449893741430536969167023835613472310999331635200000⟩,
  ⟨1, 8, 4, 3, 3, 7, 27155156668433424157436225099859971926262808576000000⟩,
  ⟨1, 8, 5, 3, 4, 7, 6505176850013374042463390335918858392928518144000000⟩,
  ⟨1, 8, 6, 3, 5, 7, 1154015139108069434477302869900114717374309990400000⟩,
  ⟨1, 8, 7, 3, 6, 7, -99121932362145562654324015579054827359541657600000⟩,
  ⟨1, 8, 8, 3, 7, 7, -179583194030786588919848197193693646569865216000000⟩,
  ⟨1, 8, 2, 4, 0, 7, 137107895743302149285959516201221122400313776537600000⟩,
  ⟨1, 8, 3, 4, 1, 7, -59508795864645730909777474315481302192559122022400000⟩,
  ⟨1, 8, 4, 4, 2, 7, -90532767144344128877418667361985412666674590515200000⟩,
  ⟨1, 8, 5, 4, 3, 7, -606779525130646114785523263196767388491055104000000⟩,
  ⟨1, 8, 6, 4, 4, 7, -533315753655662061920271929457424537592266752000000⟩,
  ⟨1, 8, 7, 4, 5, 7, -341267894471530171234104218493176038085885952000000⟩,
  ⟨1, 8, 8, 4, 6, 7, 229065239180383368555759970313315045907785318400000⟩,
  ⟨1, 8, 3, 5, 0, 7, 71478384501910265321096495665327727577356933529600000⟩,
  ⟨1, 8, 4, 5, 1, 7, 87284887226134161273898219308725530662520907366400000⟩,
  ⟨1, 8, 5, 5, 2, 7, -47128996750141246828664664201939237899436294144000000⟩,
  ⟨1, 8, 6, 5, 3, 7, -197554035762452844344718751023291549799887667200000⟩,
  ⟨1, 8, 7, 5, 4, 7, 216248400628270258467202242676862193110089728000000⟩,
  ⟨1, 8, 8, 5, 5, 7, 76569587084165796386441116210062139134364876800000⟩,
  ⟨1, 8, 4, 6, 0, 7, 272330908727409885097427855092506939428417883340800000⟩,
  ⟨1, 8, 5, 6, 1, 7, 60210570910096337020110081408335766894768291840000000⟩,
  ⟨1, 8, 6, 6, 2, 7, -14155333906052508947543575353885254970728723251200000⟩,
  ⟨1, 8, 7, 6, 3, 7, 648424817540069891759187268385657418089811148800000⟩,
  ⟨1, 8, 8, 6, 4, 7, -114062129538750027537389554683843570075225292800000⟩,
  ⟨1, 8, 5, 7, 0, 7, 262694528448711239488724074081088769450754179072000000⟩,
  ⟨1, 8, 6, 7, 1, 7, 28062299571437360227288037939266719558997219737600000⟩,
  ⟨1, 8, 7, 7, 2, 7, -1151480413993541121730739770870667635821065011200000⟩,
  ⟨1, 8, 8, 7, 3, 7, -546294698769080160329421881155662491621208883200000⟩
]

def collectedFourData_10_2_15 : List CollectedFourTerm := [
  ⟨2, 0, 8, 2, 8, 0, 12273470924112170725411678455544734093755075788800000⟩,
  ⟨2, 0, 8, 3, 7, 0, 7518197598960423538521648151082881327262859264000000⟩,
  ⟨2, 0, 8, 4, 6, 0, -9589748865453510764463276763569677700236417433600000⟩,
  ⟨2, 0, 8, 5, 5, 0, -3205563242576462863173251561582486869337387827200000⟩,
  ⟨2, 0, 8, 6, 4, 0, 4775177505104023443017797241703688213208707891200000⟩,
  ⟨2, 0, 8, 7, 3, 0, 22870466887377015041055879703927084402818731212800000⟩
]

def collectedFourData_10_2_16 : List CollectedFourTerm := [
  ⟨2, 1, 7, 1, 8, 1, 24626943702468280027813728072457544427100333670400000⟩,
  ⟨2, 1, 7, 2, 7, 1, -1454002964229472337223993751664265752664342528000000⟩,
  ⟨2, 1, 8, 2, 8, 1, -23505227723549774451038493845426132886457260441600000⟩,
  ⟨2, 1, 7, 3, 6, 1, -1135316185372738929884725024547862681926133350400000⟩,
  ⟨2, 1, 8, 3, 7, 1, -14398286167528694924470215214113118235758952448000000⟩,
  ⟨2, 1, 7, 4, 5, 1, -3908791474383818175760323114124293916179038208000000⟩,
  ⟨2, 1, 8, 4, 6, 1, 18365565233165152388627048051250512068540052275200000⟩,
  ⟨2, 1, 7, 5, 4, 1, 2476851524617809118545792656379218147527360512000000⟩,
  ⟨2, 1, 8, 5, 5, 1, 6139053448277168341468114068556639828013639270400000⟩,
  ⟨2, 1, 7, 6, 3, 1, 7426884976989683453558108340953996524115931955200000⟩,
  ⟨2, 1, 8, 6, 4, 1, -9145060543332943846232913682272059519966537318400000⟩,
  ⟨2, 1, 7, 7, 2, 1, -13188749654015239877475012351310228286367124684800000⟩,
  ⟨2, 1, 8, 7, 3, 1, -43799796785731830206083987994836001575602330009600000⟩
]

def collectedFourData_10_2_17 : List CollectedFourTerm := [
  ⟨2, 2, 6, 0, 8, 2, 993607991822548920139024622803169771467151769600000⟩,
  ⟨2, 2, 6, 1, 7, 2, -3323049092340194122866585264497836479473516544000000⟩,
  ⟨2, 2, 7, 1, 8, 2, -6247084551870862623699176998033912402423893196800000⟩,
  ⟨2, 2, 6, 2, 6, 2, 229388809565897195931856444776603732917039923200000⟩,
  ⟨2, 2, 7, 2, 7, 2, 368835027437935425225581202168160829860478976000000⟩,
  ⟨2, 2, 8, 2, 8, 2, 2981270164378483147506638241992889459784915353600000⟩,
  ⟨2, 2, 6, 3, 5, 2, -558822895961337228640347497173295183388947251200000⟩,
  ⟨2, 2, 7, 3, 6, 2, 287994169671169700210701998798767404557847756800000⟩,
  ⟨2, 2, 8, 3, 7, 2, 1826197196397726467516140370431048669156343808000000⟩,
  ⟨2, 2, 6, 4, 4, 2, 258254024422942018980440041131875679816646656000000⟩,
  ⟨2, 2, 7, 4, 5, 2, 991538013450702357907356372594211468697665536000000⟩,
  ⟨2, 2, 8, 4, 6, 2, -2329384438455176118142247530240371128689439539200000⟩,
  ⟨2, 2, 6, 5, 3, 2, 95664012223400410974573839691958730433862041600000⟩,
  ⟨2, 2, 7, 5, 4, 2, -628299681992893392801785039132456141092552704000000⟩,
  ⟨2, 2, 8, 5, 5, 2, -778642823550979877471867082045143890440644198400000⟩,
  ⟨2, 2, 6, 6, 2, 2, 6854610844008344176782067722963286032356317593600000⟩,
  ⟨2, 2, 7, 6, 3, 2, -1883968184148805987813478799731909548424193638400000⟩,
  ⟨2, 2, 8, 6, 4, 2, 1159907764771741379950907129543836503351125606400000⟩,
  ⟨2, 2, 6, 7, 1, 2, -13588951290505269508034801450282126952652131532800000⟩,
  ⟨2, 2, 7, 7, 2, 2, 3345572849700914313521900037926088042109049241600000⟩,
  ⟨2, 2, 8, 7, 3, 2, 5555318540152512226965705542411589664072374681600000⟩
]

def collectedFourData_10_2_18 : List CollectedFourTerm := [
  ⟨2, 3, 5, 0, 7, 3, 504680884280110899652792354646429576263945420800000⟩,
  ⟨2, 3, 6, 0, 8, 3, 31090846858603160591059278805045506630109416652800000⟩,
  ⟨2, 3, 5, 1, 6, 3, -83268431017176044960390771467349769859360201113600000⟩,
  ⟨2, 3, 6, 1, 7, 3, -103981058207934341605795413081189160639153569792000000⟩,
  ⟨2, 3, 7, 1, 8, 3, -97738318689796771897891543629316395426047537971200000⟩,
  ⟨2, 3, 5, 2, 5, 3, 14565466506190415291484124392277308018293892710400000⟩,
  ⟨2, 3, 6, 2, 6, 3, 7177772731284851611994964497537569049068280217600000⟩,
  ⟨2, 3, 7, 2, 7, 3, 5770582286243092776358924238226715240808054784000000⟩,
  ⟨2, 3, 8, 2, 8, 3, 31095500736594947972699820915074011250034317721600000⟩,
  ⟨2, 3, 5, 3, 4, 3, -19713750896824978452587611791153868218507146035200000⟩,
  ⟨2, 3, 6, 3, 5, 3, -17486048041487553292787457298428169230380276121600000⟩,
  ⟨2, 3, 7, 3, 6, 3, 4505792374411591661955233930378600899381769011200000⟩,
  ⟨2, 3, 8, 3, 7, 3, 19047759221644253632280082136761641530030030848000000⟩,
  ⟨2, 3, 5, 4, 3, 3, 1838827857184961364158961747107101587499332403200000⟩,
  ⟨2, 3, 6, 4, 4, 3, 8080990078616065720760445451730517034750967808000000⟩,
  ⟨2, 3, 7, 4, 5, 3, 15513037729362888614168266099960956828279373824000000⟩,
  ⟨2, 3, 8, 4, 6, 3, -24296146114921524562690595455059510216459760435200000⟩,
  ⟨2, 3, 5, 5, 2, 3, 142823065901374899263187089054269876579855446835200000⟩,
  ⟨2, 3, 6, 5, 3, 3, 2993409049037184769340874906590283286801337548800000⟩,
  ⟨2, 3, 7, 5, 4, 3, -9830018153496700638583173840500987389947150336000000⟩,
  ⟨2, 3, 8, 5, 5, 3, -8121467414316506182105756461726930078437631590400000⟩,
  ⟨2, 3, 5, 6, 1, 3, -182466399245520175154606214112712461090314780672000000⟩,
  ⟨2, 3, 6, 6, 2, 3, 214486656488613344016173413308414045099209313484800000⟩,
  ⟨2, 3, 7, 6, 3, 3, -29475490727691389549668780073991238790755752345600000⟩,
  ⟨2, 3, 8, 6, 4, 3, 12098169828684781460686282885051616066282088038400000⟩,
  ⟨2, 3, 5, 7, 0, 3, -796088194863779774992011632769192546054279109017600000⟩,
  ⟨2, 3, 6, 7, 1, 3, -425209949013343975023735608469502850347890533990400000⟩,
  ⟨2, 3, 7, 7, 2, 3, 52342922953727767582300569119452732004074153574400000⟩,
  ⟨2, 3, 8, 7, 3, 3, 57943561714523418614123492848644088327956961689600000⟩
]

def collectedFourData_10_2_19 : List CollectedFourTerm := [
  ⟨2, 4, 4, 0, 6, 4, 25512003468642075488908551472252196170742995353600000⟩,
  ⟨2, 4, 5, 0, 7, 4, 329800114128930685497107714871006078309079449600000⟩,
  ⟨2, 4, 6, 0, 8, 4, 10158661801663687195245557643468306339391655116800000⟩,
  ⟨2, 4, 4, 1, 5, 4, -39533933188606485208721375634941397948245401927680000⟩,
  ⟨2, 4, 5, 1, 6, 4, -54414460519886796399786550848020653275845178163200000⟩,
  ⟨2, 4, 6, 1, 7, 4, -33974899716223699122037940679271609058828746752000000⟩,
  ⟨2, 4, 7, 1, 8, 4, -21290092850550694559025664356067210834136059084800000⟩,
  ⟨2, 4, 4, 2, 4, 4, 10540511031525388943341304766633357321543635435520000⟩,
  ⟨2, 4, 5, 2, 5, 4, 9518277124632568967168722273641693099657579724800000⟩,
  ⟨2, 4, 6, 2, 6, 4, 2345274350291615929632100822965512814393399705600000⟩,
  ⟨2, 4, 7, 2, 7, 4, 1256991467857978631427479405059840914946523136000000⟩,
  ⟨2, 4, 8, 2, 8, 4, 5080091207760757174314259180344940567938780364800000⟩,
  ⟨2, 4, 4, 3, 3, 4, -13444245191209631723698571714935213890304632422400000⟩,
  ⟨2, 4, 5, 3, 4, 4, -12882590758229775672286635594911646769681426022400000⟩,
  ⟨2, 4, 6, 3, 5, 4, -5713412989648505748565207126210983687418911129600000⟩,
  ⟨2, 4, 7, 3, 6, 4, 981485453223172601005033096053938065595223244800000⟩,
  ⟨2, 4, 8, 3, 7, 4, 3111844217242048757644887788118327892371308544000000⟩,
  ⟨2, 4, 4, 4, 2, 4, 44821863272183682295723978077855548154512387604480000⟩,
  ⟨2, 4, 5, 4, 3, 4, 1201641782070082037201196081007570732615886438400000⟩,
  ⟨2, 4, 6, 4, 4, 4, 2640392704791974521584696349993998019196878848000000⟩,
  ⟨2, 4, 7, 4, 5, 4, 3379166104754269913311812830351531364682039296000000⟩,
  ⟨2, 4, 8, 4, 6, 4, -3969276433475407949252832701430117783762999705600000⟩,
  ⟨2, 4, 4, 5, 1, 4, -43213870561805416911088539360564349108164608655360000⟩,
  ⟨2, 4, 5, 5, 2, 4, 93332370814294238197618150478009488075435435622400000⟩,
  ⟨2, 4, 6, 5, 3, 4, 978070179352286673997959289835832841320844492800000⟩,
  ⟨2, 4, 7, 5, 4, 4, -2141248202506590591779318876692968838313017344000000⟩,
  ⟨2, 4, 8, 5, 5, 4, -1326809159790447156229401873487520825114571571200000⟩,
  ⟨2, 4, 4, 6, 0, 4, -134828296326211113969557327566346022229246916689920000⟩,
  ⟨2, 4, 5, 6, 1, 4, -119238594466890003546771792725151544419563864064000000⟩,
  ⟨2, 4, 6, 6, 2, 4, 70081635735004550063136512400578333503545724108800000⟩,
  ⟨2, 4, 7, 6, 3, 4, -6420572226127379711060642729552324108120122982400000⟩,
  ⟨2, 4, 8, 6, 4, 4, 1976485495355559278550569727833029297124356915200000⟩,
  ⟨2, 4, 5, 7, 0, 4, -520229685135145669226313366806078299091995145011200000⟩,
  ⟨2, 4, 6, 7, 1, 4, -138933625268362646323881611808159584193308157542400000⟩,
  ⟨2, 4, 7, 7, 2, 4, 11401727640629240905900416196963910076363020697600000⟩,
  ⟨2, 4, 8, 7, 3, 4, 9466275552394478151680555616351156115402968268800000⟩
]

def collectedFourData_10_2_20 : List CollectedFourTerm := [
  ⟨2, 5, 3, 0, 5, 5, 21949854844140572880607229972824007493329879040000000⟩,
  ⟨2, 5, 4, 0, 6, 5, 23037812710678506388023426987339021824362020864000000⟩,
  ⟨2, 5, 5, 0, 7, 5, 148907812563634629875815800707932009059581952000000⟩,
  ⟨2, 5, 6, 0, 8, 5, 3057820060604185539891344769536690896811065344000000⟩,
  ⟨2, 5, 3, 1, 4, 5, -20997430105576764042935187551482748648732334489600000⟩,
  ⟨2, 5, 4, 1, 5, 5, -35699875536433951197479467000016652797480219443200000⟩,
  ⟨2, 5, 5, 1, 6, 5, -24568633971663663023797967275685053530409795584000000⟩,
  ⟨2, 5, 6, 1, 7, 5, -10226655039571287107032612601067151774879580160000000⟩,
  ⟨2, 5, 7, 1, 8, 5, -4806337262837956159182421160661241013194457088000000⟩,
  ⟨2, 5, 3, 2, 3, 5, 14565466506190415291484124392277308018293892710400000⟩,
  ⟨2, 5, 4, 2, 4, 5, 9518277124632568967168722273641693099657579724800000⟩,
  ⟨2, 5, 5, 2, 5, 5, 4297590465506711341932107397114882500094590976000000⟩,
  ⟨2, 5, 6, 2, 6, 5, 705942091188396888187954185806219718791528448000000⟩,
  ⟨2, 5, 7, 2, 7, 5, 283771657241922749769134119461121169723228160000000⟩,
  ⟨2, 5, 8, 2, 8, 5, 917483332435328036853759683561591737344747110400000⟩,
  ⟨2, 5, 3, 3, 2, 5, -9604654358724263949476616741131766933978768998400000⟩,
  ⟨2, 5, 4, 3, 3, 5, -12140402972750669315202031811639864360882405376000000⟩,
  ⟨2, 5, 5, 3, 4, 5, -5816609296898398702644221994356520554424434688000000⟩,
  ⟨2, 5, 6, 3, 5, 5, -1719772662517672453806563358024113603758522368000000⟩,
  ⟨2, 5, 7, 3, 6, 5, 221574895885807006481104418310312330094706688000000⟩,
  ⟨2, 5, 8, 3, 7, 5, 562010618646612454133639354057229952836698112000000⟩,
  ⟨2, 5, 3, 4, 1, 5, 8868306561945242900557905889613422876081048780800000⟩,
  ⟨2, 5, 4, 4, 2, 5, 40474974561579161859658225139561508047458349875200000⟩,
  ⟨2, 5, 5, 4, 3, 5, 542552417623397221682650614335263527149764608000000⟩,
  ⟨2, 5, 6, 4, 4, 5, 794774541983825928959939454369838913122467840000000⟩,
  ⟨2, 5, 7, 4, 5, 5, 762862429986036049573028518665267242084597760000000⟩,
  ⟨2, 5, 8, 4, 6, 5, -716866060195653086536853072747162220215717068800000⟩,
  ⟨2, 5, 3, 5, 0, 5, -10652076169669773569492804716704151665548407603200000⟩,
  ⟨2, 5, 4, 5, 1, 5, -39022927294990946901001448890573894587521590886400000⟩,
  ⟨2, 5, 5, 5, 2, 5, 42140431685543246565403368064119342667753586688000000⟩,
  ⟨2, 5, 6, 5, 3, 5, 294405175946733233756106589238897960156135424000000⟩,
  ⟨2, 5, 7, 5, 4, 5, -483396718696133649724286503716073151020400640000000⟩,
  ⟨2, 5, 8, 5, 5, 5, -239626660161253164800471990420226904579217817600000⟩,
  ⟨2, 5, 4, 6, 0, 5, -121752454395869726259662954988323269623856024780800000⟩,
  ⟨2, 5, 5, 6, 1, 5, -53837332112885848782424160676634624683336007680000000⟩,
  ⟨2, 5, 6, 6, 2, 5, 21095005997281706625576368607417111190337224704000000⟩,
  ⟨2, 5, 7, 6, 3, 5, -1449473976266865161833858788684685576916434944000000⟩,
  ⟨2, 5, 8, 6, 4, 5, 356960618348470579106062502936855325976402329600000⟩,
  ⟨2, 5, 5, 7, 0, 5, -234888531341922436618694281641583262283904057344000000⟩,
  ⟨2, 5, 6, 7, 1, 5, -41819880879240282450410084950829616044433211392000000⟩,
  ⟨2, 5, 7, 7, 2, 5, 2573992927347347369343615009209999185051385856000000⟩,
  ⟨2, 5, 8, 7, 3, 5, 1709644509195784842460611256114570598990374502400000⟩
]

def collectedFourData_10_2_21 : List CollectedFourTerm := [
  ⟨2, 6, 2, 0, 4, 6, -1573678291185118444917270723254497260929758003200000⟩,
  ⟨2, 6, 3, 0, 5, 6, 10816754100458966467077784688238888203593973760000000⟩,
  ⟨2, 6, 4, 0, 6, 6, 5676446538560114461148545931813450072413175808000000⟩,
  ⟨2, 6, 5, 0, 7, 6, 24460286162485183488271762233920296002256896000000⟩,
  ⟨2, 6, 6, 0, 8, 6, 376718751830782990000043621395273888441565184000000⟩,
  ⟨2, 6, 2, 1, 3, 6, 939557514325854049952373660420197306136841420800000⟩,
  ⟨2, 6, 3, 1, 4, 6, -10347405019593005519422156104161851649558996582400000⟩,
  ⟨2, 6, 4, 1, 5, 6, -8796340063216402403231205445819792722137343590400000⟩,
  ⟨2, 6, 5, 1, 6, 6, -4035757474520916484163547526817174643573522432000000⟩,
  ⟨2, 6, 6, 1, 7, 6, -1259908250176782331512063777255160320633077760000000⟩,
  ⟨2, 6, 7, 1, 8, 6, -473706716196070312065453105742567880926848614400000⟩,
  ⟨2, 6, 2, 2, 2, 6, 229388809565897195931856444776603732917039923200000⟩,
  ⟨2, 6, 3, 2, 3, 6, 7177772731284851611994964497537569049068280217600000⟩,
  ⟨2, 6, 4, 2, 4, 6, 2345274350291615929632100822965512814393399705600000⟩,
  ⟨2, 6, 5, 2, 5, 6, 705942091188396888187954185806219718791528448000000⟩,
  ⟨2, 6, 6, 2, 6, 6, 86970985272677899497780610697843697650761728000000⟩,
  ⟨2, 6, 7, 2, 7, 6, 27968187114321551340183230987314807185604608000000⟩,
  ⟨2, 6, 8, 2, 8, 6, 75355028303462147873208271137575833068738969600000⟩,
  ⟨2, 6, 2, 3, 1, 6, 1314642040438886238033384196006358540007505920000000⟩,
  ⟨2, 6, 3, 3, 2, 6, -4733114872782637501964809344255733152895048089600000⟩,
  ⟨2, 6, 4, 3, 3, 6, -2991358133554589733366541712842622990624489472000000⟩,
  ⟨2, 6, 5, 3, 4, 6, -955463151650999037270382015934477500441165824000000⟩,
  ⟨2, 6, 6, 3, 5, 6, -211873360111434790065560977350561444919246848000000⟩,
  ⟨2, 6, 7, 3, 6, 6, 21838150462952758629482011805595004949653094400000⟩,
  ⟨2, 6, 8, 3, 7, 6, 46159232083866723763755416131513220792844288000000⟩,
  ⟨2, 6, 2, 4, 0, 6, -5034511174852330869680865558614600236371699302400000⟩,
  ⟨2, 6, 3, 4, 1, 6, 4370247186106358709361848213204620932478612275200000⟩,
  ⟨2, 6, 4, 4, 2, 6, 9972909847552017740099633134409635800824571494400000⟩,
  ⟨2, 6, 5, 4, 3, 6, 89122170050985129867395160486309644136873984000000⟩,
  ⟨2, 6, 6, 4, 4, 6, 97915007263007590118882286742878491498250240000000⟩,
  ⟨2, 6, 7, 4, 5, 6, 75186787122105312270347874829273174363865088000000⟩,
  ⟨2, 6, 8, 4, 6, 6, -58877867691010708870932805851388206279504691200000⟩,
  ⟨2, 6, 3, 5, 0, 6, -5249277929390705111073732271404162625684950220800000⟩,
  ⟨2, 6, 4, 5, 1, 6, -9615129845441409708812479529704121052242431180800000⟩,
  ⟨2, 6, 5, 5, 2, 6, 6922182256881620265620103731797238398083661824000000⟩,
  ⟨2, 6, 6, 5, 3, 6, 36270267123978978596602881877572043684184064000000⟩,
  ⟨2, 6, 7, 5, 4, 6, -47642988769017908072322779457692860082552832000000⟩,
  ⟨2, 6, 8, 5, 5, 6, -19681091874209227203821758134913234236761702400000⟩,
  ⟨2, 6, 4, 6, 0, 6, -29999432107384212396055704701145000924379978137600000⟩,
  ⟨2, 6, 5, 6, 1, 6, -8843569232763953728378375425579739479948656640000000⟩,
  ⟨2, 6, 6, 6, 2, 6, 2598872455427820338792172112432595624886534144000000⟩,
  ⟨2, 6, 7, 6, 3, 6, -142858380500666661384438585675716655198712627200000⟩,
  ⟨2, 6, 8, 6, 4, 6, 29318001262727465289483646384357718790399590400000⟩,
  ⟨2, 6, 5, 7, 0, 6, -38583876789231740176400972665172589682372902912000000⟩,
  ⟨2, 6, 6, 7, 1, 6, -5152145323890175214493605221987816822655680512000000⟩,
  ⟨2, 6, 7, 7, 2, 6, 253689591563464726831146050971184067670494412800000⟩,
  ⟨2, 6, 8, 7, 3, 6, 140417058081420858891875208708866716003309977600000⟩
]

def collectedFourData_10_2_22 : List CollectedFourTerm := [
  ⟨2, 7, 1, 0, 3, 7, -1352508879285030363940207362529923410033639424000000⟩,
  ⟨2, 7, 2, 0, 4, 7, -2530322541915477942843079749338673398862053376000000⟩,
  ⟨2, 7, 3, 0, 5, 7, 8696147390498750460915093813808334769645158400000000⟩,
  ⟨2, 7, 4, 0, 6, 7, 3042392403189336926731145620068527008886292480000000⟩,
  ⟨2, 7, 5, 0, 7, 7, 9832443804640187730224311923249787510456320000000⟩,
  ⟨2, 7, 6, 0, 8, 7, 121145466015399410989930446951644138594893824000000⟩,
  ⟨2, 7, 1, 1, 2, 7, -396918043595620835920946408205632418003025920000000⟩,
  ⟨2, 7, 2, 1, 3, 7, 1510717642380644241474022446158738614275538944000000⟩,
  ⟨2, 7, 3, 1, 4, 7, -8318813418874829596767434695387299373400457216000000⟩,
  ⟨2, 7, 4, 1, 5, 7, -4714554783949046698176810564066084600491802624000000⟩,
  ⟨2, 7, 5, 1, 6, 7, -1622276955951682114994920670932643184314941440000000⟩,
  ⟨2, 7, 6, 1, 7, 7, -405162130535177200788896602993613230949007360000000⟩,
  ⟨2, 7, 7, 1, 8, 7, -126945766590472135122257884885158874193068032000000⟩,
  ⟨2, 7, 1, 2, 1, 7, -1454002964229472337223993751664265752664342528000000⟩,
  ⟨2, 7, 2, 2, 2, 7, 368835027437935425225581202168160829860478976000000⟩,
  ⟨2, 7, 3, 2, 3, 7, 5770582286243092776358924238226715240808054784000000⟩,
  ⟨2, 7, 4, 2, 4, 7, 1256991467857978631427479405059840914946523136000000⟩,
  ⟨2, 7, 5, 2, 5, 7, 283771657241922749769134119461121169723228160000000⟩,
  ⟨2, 7, 6, 2, 6, 7, 27968187114321551340183230987314807185604608000000⟩,
  ⟨2, 7, 7, 2, 7, 7, 7495023464906422133939215531540639635210240000000⟩,
  ⟨2, 7, 8, 2, 8, 7, 17309085692597846245883158562118511261384704000000⟩,
  ⟨2, 7, 1, 3, 0, 7, -1276090101938582767365108199063954278448103424000000⟩,
  ⟨2, 7, 2, 3, 1, 7, 2113817295507806303723705597767084907534745600000000⟩,
  ⟨2, 7, 3, 3, 2, 7, -3805195548277565190934566474492262501280907264000000⟩,
  ⟨2, 7, 4, 3, 3, 7, -1603271553589518218417160562221122710740664320000000⟩,
  ⟨2, 7, 5, 3, 4, 7, -384073092342692426350911436407241336506286080000000⟩,
  ⟨2, 7, 6, 3, 5, 7, -68134375637552016112217580861867643191164928000000⟩,
  ⟨2, 7, 7, 3, 6, 7, 5852272422268454848943545384940987253522432000000⟩,
  ⟨2, 7, 8, 3, 7, 7, 10602797472606781878529011528890198387589120000000⟩,
  ⟨2, 7, 2, 4, 0, 7, -8095007209930237217221392079788720426458284032000000⟩,
  ⟨2, 7, 3, 4, 1, 7, 3513467470031583189941530148861942892664455168000000⟩,
  ⟨2, 7, 4, 4, 2, 7, 5345158269662978824823498368975732201293348864000000⟩,
  ⟨2, 7, 5, 4, 3, 7, 35824958177221358782678822022134300441313280000000⟩,
  ⟨2, 7, 6, 4, 4, 7, 31487572962936831597800861723745019641200640000000⟩,
  ⟨2, 7, 7, 4, 5, 7, 20148847382479809152122540099630065663344640000000⟩,
  ⟨2, 7, 8, 4, 6, 7, -13524274095645444980934231539872998661029888000000⟩,
  ⟨2, 7, 3, 5, 0, 7, -4220165693305050707396542507548423213885161472000000⟩,
  ⟨2, 7, 4, 5, 1, 7, -5153399719126098551480260400990778340040245248000000⟩,
  ⟨2, 7, 5, 5, 2, 7, 2782549950321217848645952621318111724914606080000000⟩,
  ⟨2, 7, 6, 5, 3, 7, 11663816552490516980281994443146480272277504000000⟩,
  ⟨2, 7, 7, 5, 4, 7, -12767553266947759627380104897678374034472960000000⟩,
  ⟨2, 7, 8, 5, 5, 7, -4520756125293992346565756978910962517016576000000⟩,
  ⟨2, 7, 4, 6, 0, 7, -16078728782787327603765330377467919125557805056000000⟩,
  ⟨2, 7, 5, 6, 1, 7, -3554901072537653978837638252050343242026188800000000⟩,
  ⟨2, 7, 6, 6, 2, 7, 835747127525022325925083738886242567804944384000000⟩,
  ⟨2, 7, 7, 6, 3, 7, -38283743942157197899373018308736614574063616000000⟩,
  ⟨2, 7, 8, 6, 4, 7, 6734358776279913007671558168404585607069696000000⟩,
  ⟨2, 7, 5, 7, 0, 7, -15509785853492128499808801564768180607427543040000000⟩,
  ⟨2, 7, 6, 7, 1, 7, -1656830309636670498361414671001264779304108032000000⟩,
  ⟨2, 7, 7, 7, 2, 7, 67984722563481697358135067663667691293507584000000⟩,
  ⟨2, 7, 8, 7, 3, 7, 32253864748693020150656731604339010645786624000000⟩
]

def collectedFourData_10_2_23 : List CollectedFourTerm := [
  ⟨2, 8, 0, 0, 2, 8, -10360280526650034221496974501387895406964873625600000⟩,
  ⟨2, 8, 1, 0, 3, 8, -21864487203824184209264182982834026260214893772800000⟩,
  ⟨2, 8, 2, 0, 4, 8, -20452436832985744651948111380315536762154359193600000⟩,
  ⟨2, 8, 3, 0, 5, 8, 46860272356126789648685983391987381968211804160000000⟩,
  ⟨2, 8, 4, 0, 6, 8, 12295732543306752093925023120928316857792856064000000⟩,
  ⟨2, 8, 5, 0, 7, 8, 31790008190189511288037840137485068125654220800000⟩,
  ⟨2, 8, 6, 0, 8, 8, 326403709439998951025766875840538214346312908800000⟩,
  ⟨2, 8, 0, 1, 1, 8, 76331577568473640276555581865597789251432559411200000⟩,
  ⟨2, 8, 1, 1, 2, 8, -6416526810345972217275350222259198067394740224000000⟩,
  ⟨2, 8, 2, 1, 3, 8, 12211035012902863386852010440204547682654905958400000⟩,
  ⟨2, 8, 3, 1, 4, 8, -44826961294859021220113085459431761404282431078400000⟩,
  ⟨2, 8, 4, 1, 5, 8, -19053723846876583716130308678580165288932881203200000⟩,
  ⟨2, 8, 5, 1, 6, 8, -5245104751284864985934451808098142442323810713600000⟩,
  ⟨2, 8, 6, 1, 7, 8, -1091633279238732683758000683178330391033413632000000⟩,
  ⟨2, 8, 7, 1, 8, 8, -293169882991746059810353849618780609982968627200000⟩,
  ⟨2, 8, 0, 2, 0, 8, 12273470924112170725411678455544734093755075788800000⟩,
  ⟨2, 8, 1, 2, 1, 8, -23505227723549774451038493845426132886457260441600000⟩,
  ⟨2, 8, 2, 2, 2, 8, 2981270164378483147506638241992889459784915353600000⟩,
  ⟨2, 8, 3, 2, 3, 8, 31095500736594947972699820915074011250034317721600000⟩,
  ⟨2, 8, 4, 2, 4, 8, 5080091207760757174314259180344940567938780364800000⟩,
  ⟨2, 8, 5, 2, 5, 8, 917483332435328036853759683561591737344747110400000⟩,
  ⟨2, 8, 6, 2, 6, 8, 75355028303462147873208271137575833068738969600000⟩,
  ⟨2, 8, 7, 2, 7, 8, 17309085692597846245883158562118511261384704000000⟩,
  ⟨2, 8, 8, 2, 8, 8, 34977060819349497332757437369221292127525273600000⟩,
  ⟨2, 8, 1, 3, 0, 8, -20629110930134543482318741357983757734052154572800000⟩,
  ⟨2, 8, 2, 3, 1, 8, 17085851308157180059966219734899116092854108160000000⟩,
  ⟨2, 8, 3, 3, 2, 8, -20504769727733553005685835709518596785154136473600000⟩,
  ⟨2, 8, 4, 3, 3, 8, -6479571207370580733447258841324299268103602176000000⟩,
  ⟨2, 8, 5, 3, 4, 8, -1241775391123367903022424460637894692197053235200000⟩,
  ⟨2, 8, 6, 3, 5, 8, -183575280858206615435748924669716816811628953600000⟩,
  ⟨2, 8, 7, 3, 6, 8, 13515299228584414574253687589435813267714867200000⟩,
  ⟨2, 8, 8, 3, 7, 8, 21425435094657074260896533726462641761681408000000⟩,
  ⟨2, 8, 2, 4, 0, 8, -65431430531512353332190193899467626233415807795200000⟩,
  ⟨2, 8, 3, 4, 1, 8, 18932756675669569854236658760250672207566680883200000⟩,
  ⟨2, 8, 4, 4, 2, 8, 21602287862842190404973177669793894112842429235200000⟩,
  ⟨2, 8, 5, 4, 3, 8, 115828347102232959223871795049822117076087603200000⟩,
  ⟨2, 8, 6, 4, 4, 8, 84837352601035478952791444393806161896275968000000⟩,
  ⟨2, 8, 7, 4, 5, 8, 46531959183769305288549596805343073160658944000000⟩,
  ⟨2, 8, 8, 4, 6, 8, -27328962718304458673041294550930285541929779200000⟩,
  ⟨2, 8, 3, 5, 0, 8, -22740887992805200935837992498588450083771829452800000⟩,
  ⟨2, 8, 4, 5, 1, 8, -20827301753942510199116442400175012571540514406400000⟩,
  ⟨2, 8, 5, 5, 2, 8, 8996469999510968316674446657041518634934154035200000⟩,
  ⟨2, 8, 6, 5, 3, 8, 31425963465084394083646131221240496064875724800000⟩,
  ⟨2, 8, 7, 5, 4, 8, -29485521241815825138980703169383695715926016000000⟩,
  ⟨2, 8, 8, 5, 5, 8, -9135246352814305197775680220082954723288678400000⟩,
  ⟨2, 8, 4, 6, 0, 8, -64981673153756450429386670955626653478143446220800000⟩,
  ⟨2, 8, 5, 6, 1, 8, -11493616079245015531633827699164610203769372672000000⟩,
  ⟨2, 8, 6, 6, 2, 8, 2251763698224705349537339487520806266754354380800000⟩,
  ⟨2, 8, 7, 6, 3, 8, -88412879243273471318064261372537076033624473600000⟩,
  ⟨2, 8, 8, 6, 4, 8, 13608348856808402239596902293530798253827686400000⟩,
  ⟨2, 8, 5, 7, 0, 8, -50145846658987671225234583352443023525620062617600000⟩,
  ⟨2, 8, 6, 7, 1, 8, -4464018149133934910934707471524698794353911398400000⟩,
  ⟨2, 8, 7, 7, 2, 8, 157004630358884030375507586342648291699091046400000⟩,
  ⟨2, 8, 8, 7, 3, 8, 65176486442409545067474454807714303816866201600000⟩
]

def collectedFourData_10_2_24 : List CollectedFourTerm := [
  ⟨3, 0, 7, 1, 8, 1, 21613572924435090276243175024472511573847651123200000⟩,
  ⟨3, 0, 7, 2, 7, 1, -1276090101938582767365108199063954278448103424000000⟩,
  ⟨3, 0, 8, 2, 8, 1, -20629110930134543482318741357983757734052154572800000⟩,
  ⟨3, 0, 7, 3, 6, 1, -996398069582047672464239983158272491387040563200000⟩,
  ⟨3, 0, 8, 3, 7, 1, -12636501379486081293238912809518887503642230784000000⟩,
  ⟨3, 0, 7, 4, 5, 1, -3430508901091829460913447943136283776321060864000000⟩,
  ⟨3, 0, 8, 4, 6, 1, 16118341287542724331492918928962158728694045081600000⟩,
  ⟨3, 0, 7, 5, 4, 1, 2173782167088795087431739448183405479142096896000000⟩,
  ⟨3, 0, 8, 5, 5, 1, 5387874394582081243508580937756387588946735923200000⟩,
  ⟨3, 0, 7, 6, 3, 1, 6518125918949065154638010946771297198986074521600000⟩,
  ⟨3, 0, 8, 6, 4, 1, -8026064270894077554918607724359742355949171507200000⟩,
  ⟨3, 0, 7, 7, 2, 1, -11574964635201817560402662273086340939978794598400000⟩,
  ⟨3, 0, 8, 7, 3, 1, -38440421732436528667874095252827610246028250316800000⟩
]

def collectedFourData_10_2_25 : List CollectedFourTerm := [
  ⟨3, 1, 6, 0, 8, 2, 5694431390258088605398675829075379933161717760000000⟩,
  ⟨3, 1, 6, 1, 7, 2, -19044608355133014465533932237506439163569766400000000⟩,
  ⟨3, 1, 7, 1, 8, 2, -35802443883848115242838279678321098154395566080000000⟩,
  ⟨3, 1, 6, 2, 6, 2, 1314642040438886238033384196006358540007505920000000⟩,
  ⟨3, 1, 7, 2, 7, 2, 2113817295507806303723705597767084907534745600000000⟩,
  ⟨3, 1, 8, 2, 8, 2, 17085851308157180059966219734899116092854108160000000⟩,
  ⟨3, 1, 6, 3, 5, 2, -3202650005381078360831404833109555972637982720000000⟩,
  ⟨3, 1, 7, 3, 6, 2, 1650513133432715052439363143210387443369902080000000⟩,
  ⟨3, 1, 8, 3, 7, 2, 10466053741067072402427233258596778120105164800000000⟩,
  ⟨3, 1, 6, 4, 4, 2, 1480070445726769263847302663955308120480153600000000⟩,
  ⟨3, 1, 7, 4, 5, 2, 5682568210900828032906898048251187493968281600000000⟩,
  ⟨3, 1, 8, 4, 6, 2, -13349852230945834894866290996639052544365035520000000⟩,
  ⟨3, 1, 6, 5, 3, 2, 548256614888674841342269835231143467637800960000000⟩,
  ⟨3, 1, 7, 5, 4, 2, -3600825940486675688014026164805932398569062400000000⟩,
  ⟨3, 1, 8, 5, 5, 2, -4462452166970650610291191095720059627152343040000000⟩,
  ⟨3, 1, 6, 6, 2, 2, 39284216189251054292794859168648790624341852160000000⟩,
  ⟨3, 1, 7, 6, 3, 2, -10797142992364796370011452472137229574120407040000000⟩,
  ⟨3, 1, 8, 6, 4, 2, 6647506098863893208279683279993625210876067840000000⟩,
  ⟨3, 1, 6, 7, 1, 2, -77879154984857558679020276090075017297715527680000000⟩,
  ⟨3, 1, 7, 7, 2, 2, 19173693459114694217255867777099445975342120960000000⟩,
  ⟨3, 1, 8, 7, 3, 2, 31837888320424130696925881130106618645535784960000000⟩
]

def collectedFourData_10_2_26 : List CollectedFourTerm := [
  ⟨3, 2, 5, 0, 7, 3, -332793010982906456958308131886327928388897996800000⟩,
  ⟨3, 2, 6, 0, 8, 3, -20501700901237690735234624362437352111796440268800000⟩,
  ⟨3, 2, 5, 1, 6, 3, 54908265284420902739482888994890677454724766105600000⟩,
  ⟨3, 2, 6, 1, 7, 3, 68566435789553548702074424103574499701169324032000000⟩,
  ⟨3, 2, 7, 1, 8, 3, 64449893741430536969167023835613472310999331635200000⟩,
  ⟨3, 2, 5, 2, 5, 3, -9604654358724263949476616741131766933978768998400000⟩,
  ⟨3, 2, 6, 2, 6, 3, -4733114872782637501964809344255733152895048089600000⟩,
  ⟨3, 2, 7, 2, 7, 3, -3805195548277565190934566474492262501280907264000000⟩,
  ⟨3, 2, 8, 2, 8, 3, -20504769727733553005685835709518596785154136473600000⟩,
  ⟨3, 2, 5, 3, 4, 3, 12999498738850698737786695707361826074409513779200000⟩,
  ⟨3, 2, 6, 3, 5, 3, 11530523067500555607726540311380838487690942873600000⟩,
  ⟨3, 2, 7, 3, 6, 3, -2971176951318794031703599603284167372712391475200000⟩,
  ⟨3, 2, 8, 3, 7, 3, -12560335335249446488513593790740819810774417408000000⟩,
  ⟨3, 2, 5, 4, 3, 3, -1212546538481892829943273603613376671244301107200000⟩,
  ⟨3, 2, 6, 4, 4, 3, -5328707909794747260246710344798785020853485568000000⟩,
  ⟨3, 2, 7, 4, 5, 3, -10229494907084122912837389951328606012890415104000000⟩,
  ⟨3, 2, 8, 4, 6, 3, 16021188582164862462490993362599500295217296179200000⟩,
  ⟨3, 2, 5, 5, 2, 3, -94179350991126437843137405173425238645343990579200000⟩,
  ⟨3, 2, 6, 5, 3, 3, -1973892100061500867081418064603238468026158284800000⟩,
  ⟨3, 2, 7, 5, 4, 3, 6482039326663118625860064039568299554563424256000000⟩,
  ⟨3, 2, 8, 5, 5, 3, 5355399181138480101232137623015967659601061478400000⟩,
  ⟨3, 2, 5, 6, 1, 3, 120320670545593042173615712816448229488052928512000000⟩,
  ⟨3, 2, 6, 6, 2, 3, -141435236506569235808233868424446222441152040140800000⟩,
  ⟨3, 2, 7, 6, 3, 3, 19436514468859451557100562812214841872699988377600000⟩,
  ⟨3, 2, 8, 6, 4, 3, -7977687465642001198398192169853958022083536486400000⟩,
  ⟨3, 2, 5, 7, 0, 3, 524950707722109053219454279592353667371048212889600000⟩,
  ⟨3, 2, 6, 7, 1, 3, 280388862823460734533269144119717050947572491878400000⟩,
  ⟨3, 2, 7, 7, 2, 3, -34515590893173513234255827791844636836613219942400000⟩,
  ⟨3, 2, 8, 7, 3, 3, -38208723513584537167602534334009121748740053401600000⟩
]

def collectedFourData_10_2_27 : List CollectedFourTerm := [
  ⟨3, 3, 4, 0, 6, 4, -32540132914388526472770876592021331443011551232000000⟩,
  ⟨3, 3, 5, 0, 7, 4, -420654519043428422516650714054659368395210752000000⟩,
  ⟨3, 3, 6, 0, 8, 4, -12957202897246740618597110355507745517696188416000000⟩,
  ⟨3, 3, 4, 1, 5, 4, 50424869303856519299344032331987128728726116761600000⟩,
  ⟨3, 3, 5, 1, 6, 4, 69404732558862016375527649826926855446734045184000000⟩,
  ⟨3, 3, 6, 1, 7, 4, 43334415263694108622576711068709323767273226240000000⟩,
  ⟨3, 3, 7, 1, 8, 4, 27155156668433424157436225099859971926262808576000000⟩,
  ⟨3, 3, 4, 2, 4, 4, -13444245191209631723698571714935213890304632422400000⟩,
  ⟨3, 3, 5, 2, 5, 4, -12140402972750669315202031811639864360882405376000000⟩,
  ⟨3, 3, 6, 2, 6, 4, -2991358133554589733366541712842622990624489472000000⟩,
  ⟨3, 3, 7, 2, 7, 4, -1603271553589518218417160562221122710740664320000000⟩,
  ⟨3, 3, 8, 2, 8, 4, -6479571207370580733447258841324299268103602176000000⟩,
  ⟨3, 3, 4, 3, 3, 4, 17147909453419174078300037371743380491770789888000000⟩,
  ⟨3, 3, 5, 3, 4, 4, 16431528635911672003447796225883678632614821888000000⟩,
  ⟨3, 3, 6, 3, 5, 4, 7287362527465663738145113287368574221892452352000000⟩,
  ⟨3, 3, 7, 3, 6, 4, -1251868248633506547659628147361512117843787776000000⟩,
  ⟨3, 3, 8, 3, 7, 4, -3969105153281689174829487098594479991716577280000000⟩,
  ⟨3, 3, 4, 4, 2, 4, -57169535514532382388699303361279473823994452377600000⟩,
  ⟨3, 3, 5, 4, 3, 4, -1532673956873070961920893511862140425950199808000000⟩,
  ⟨3, 3, 6, 4, 4, 4, -3367776649361119915888724863925852835686645760000000⟩,
  ⟨3, 3, 7, 4, 5, 4, -4310069741235937324914552571314727235899883520000000⟩,
  ⟨3, 3, 8, 4, 6, 4, 5062745576920174701729523952667660351776489472000000⟩,
  ⟨3, 3, 4, 5, 1, 4, 55118567757907909416370028630090146767787209523200000⟩,
  ⟨3, 3, 5, 5, 2, 4, -119043874983989394017543106741113261113252773888000000⟩,
  ⟨3, 3, 6, 5, 3, 4, -1247512124041634910053208660259818858438721536000000⟩,
  ⟨3, 3, 7, 5, 4, 4, 2731126200962712578374353521431412376632033280000000⟩,
  ⟨3, 3, 8, 5, 5, 4, 1692322849700026401430217747426755984326918144000000⟩,
  ⟨3, 3, 4, 6, 0, 4, 171971232618721334195957518219582616044537538150400000⟩,
  ⟨3, 3, 5, 6, 1, 4, 152086829136982532374026404130015757356163399680000000⟩,
  ⟨3, 3, 6, 6, 2, 4, -89387952007682554741156992344180521926138003456000000⟩,
  ⟨3, 3, 7, 6, 3, 4, 8189332283582386037124397721806737671442137088000000⟩,
  ⟨3, 3, 8, 6, 4, 4, -2520974128953982856775176267013299425115111424000000⟩,
  ⟨3, 3, 5, 7, 0, 4, 663544245794553277768509612446019425723895250944000000⟩,
  ⟨3, 3, 6, 7, 1, 4, 177207510890598167690454491370852141807370764288000000⟩,
  ⟨3, 3, 7, 7, 2, 4, -14542712544538584782444733290328537750948544512000000⟩,
  ⟨3, 3, 8, 7, 3, 4, -12074075838761975215278350176154359334128582656000000⟩
]

def collectedFourData_10_2_28 : List CollectedFourTerm := [
  ⟨3, 4, 3, 0, 5, 5, -29708212259109458993806929994533315305558507520000000⟩,
  ⟨3, 4, 4, 0, 6, 5, -31180717815869659978901898833226856645087199232000000⟩,
  ⟨3, 4, 5, 0, 7, 5, -201540508312794412317994739666179084964069376000000⟩,
  ⟨3, 4, 6, 0, 8, 5, -4138631806708375803013363247262042543957737472000000⟩,
  ⟨3, 4, 3, 1, 4, 5, 28419145133381579199019641778460678757448207564800000⟩,
  ⟨3, 4, 4, 1, 5, 5, 48318291286709191559509613102674227021418699161600000⟩,
  ⟨3, 4, 5, 1, 6, 5, 33252620490171161961609666631927809530073710592000000⟩,
  ⟨3, 4, 6, 1, 7, 5, 13841350695646063770817668012718537861842862080000000⟩,
  ⟨3, 4, 7, 1, 8, 5, 6505176850013374042463390335918858392928518144000000⟩,
  ⟨3, 4, 3, 2, 3, 5, -19713750896824978452587611791153868218507146035200000⟩,
  ⟨3, 4, 4, 2, 4, 5, -12882590758229775672286635594911646769681426022400000⟩,
  ⟨3, 4, 5, 2, 5, 5, -5816609296898398702644221994356520554424434688000000⟩,
  ⟨3, 4, 6, 2, 6, 5, -955463151650999037270382015934477500441165824000000⟩,
  ⟨3, 4, 7, 2, 7, 5, -384073092342692426350911436407241336506286080000000⟩,
  ⟨3, 4, 8, 2, 8, 5, -1241775391123367903022424460637894692197053235200000⟩,
  ⟨3, 4, 3, 3, 2, 5, 12999498738850698737786695707361826074409513779200000⟩,
  ⟨3, 4, 4, 3, 3, 5, 16431528635911672003447796225883678632614821888000000⟩,
  ⟨3, 4, 5, 3, 4, 5, 7872537875424521139468058238169846154153426944000000⟩,
  ⟨3, 4, 6, 3, 5, 5, 2327640508708305699910413561966322939575926784000000⟩,
  ⟨3, 4, 7, 3, 6, 5, -299892372182262118132883737054835500010962944000000⟩,
  ⟨3, 4, 8, 3, 7, 5, -760657911825963751768256215786874118346899456000000⟩,
  ⟨3, 4, 3, 4, 1, 5, -12002882733935369989029388034808944175161435750400000⟩,
  ⟨3, 4, 4, 4, 2, 5, -54781188486011147276238865040469152865564858777600000⟩,
  ⟨3, 4, 5, 4, 3, 5, -734322049002141385751844720595458671618555904000000⟩,
  ⟨3, 4, 6, 4, 4, 5, -1075694165590117987962456346139624260679761920000000⟩,
  ⟨3, 4, 7, 4, 5, 5, -1032502454136960290712375873641425922823290880000000⟩,
  ⟨3, 4, 8, 4, 6, 5, 970248287693305613411071550627317678095099494400000⟩,
  ⟨3, 4, 3, 5, 0, 5, 14417140436499400374675637749994289814329465241600000⟩,
  ⟨3, 4, 4, 5, 1, 5, 52815903124792558866515277260976661854036374323200000⟩,
  ⟨3, 4, 5, 5, 2, 5, -57035315180629307554275637025554516471336402944000000⟩,
  ⟨3, 4, 6, 5, 3, 5, -398465116025165641921153852283961756207808512000000⟩,
  ⟨3, 4, 7, 5, 4, 5, 654257279893371921589125231454981345058488320000000⟩,
  ⟨3, 4, 8, 5, 5, 5, 324324681578126896596120163980733390382746828800000⟩,
  ⟨3, 4, 4, 6, 0, 5, 164786864603143330816210467745522746658988123750400000⟩,
  ⟨3, 4, 5, 6, 1, 5, 72866581634854826814341107886804019007287459840000000⟩,
  ⟨3, 4, 6, 6, 2, 5, -28551210029606445890468285611886292239124529152000000⟩,
  ⟨3, 4, 7, 6, 3, 5, 1961802520187802312914413402117477718946742272000000⟩,
  ⟨3, 4, 8, 6, 4, 5, -483131296008100899139655167142500674908769484800000⟩,
  ⟨3, 4, 5, 7, 0, 5, 317911822009114455075127336186368654899750633472000000⟩,
  ⟨3, 4, 6, 7, 1, 5, 56601463045337430436229995482960320537712132096000000⟩,
  ⟨3, 4, 7, 7, 2, 5, -3483791978674270519976855269522916644516528128000000⟩,
  ⟨3, 4, 8, 7, 3, 5, -2313932475975699135788795393760613523302593331200000⟩
]

def collectedFourData_10_2_29 : List CollectedFourTerm := [
  ⟨3, 5, 2, 0, 4, 6, 3833698172355380038356423746766390284508148531200000⟩,
  ⟨3, 5, 3, 0, 5, 6, -26351110425827832690796129669356551376375644160000000⟩,
  ⟨3, 5, 4, 0, 6, 6, -13828609597176557483832162747831599116087984128000000⟩,
  ⟨3, 5, 5, 0, 7, 6, -59588643296203469943515912962099625104244736000000⟩,
  ⟨3, 5, 6, 0, 8, 6, -917739031208242234225443007991404513978220544000000⟩,
  ⟨3, 5, 2, 1, 3, 6, -2288892174258299092999556917005705122249755852800000⟩,
  ⟨3, 5, 3, 1, 4, 6, 25207711089641115446834896366067442301427672678400000⟩,
  ⟨3, 5, 4, 1, 5, 6, 21429102131397584323801400661439142650054076006400000⟩,
  ⟨3, 5, 5, 1, 6, 6, 9831663905389910099535004262457769505127923712000000⟩,
  ⟨3, 5, 6, 1, 7, 6, 3069310915130371636966654343978203675266908160000000⟩,
  ⟨3, 5, 7, 1, 8, 6, 1154015139108069434477302869900114717374309990400000⟩,
  ⟨3, 5, 2, 2, 2, 6, -558822895961337228640347497173295183388947251200000⟩,
  ⟨3, 5, 3, 2, 3, 6, -17486048041487553292787457298428169230380276121600000⟩,
  ⟨3, 5, 4, 2, 4, 6, -5713412989648505748565207126210983687418911129600000⟩,
  ⟨3, 5, 5, 2, 5, 6, -1719772662517672453806563358024113603758522368000000⟩,
  ⟨3, 5, 6, 2, 6, 6, -211873360111434790065560977350561444919246848000000⟩,
  ⟨3, 5, 7, 2, 7, 6, -68134375637552016112217580861867643191164928000000⟩,
  ⟨3, 5, 8, 2, 8, 6, -183575280858206615435748924669716816811628953600000⟩,
  ⟨3, 5, 2, 3, 1, 6, -3202650005381078360831404833109555972637982720000000⟩,
  ⟨3, 5, 3, 3, 2, 6, 11530523067500555607726540311380838487690942873600000⟩,
  ⟨3, 5, 4, 3, 3, 6, 7287362527465663738145113287368574221892452352000000⟩,
  ⟨3, 5, 5, 3, 4, 6, 2327640508708305699910413561966322939575926784000000⟩,
  ⟨3, 5, 6, 3, 5, 6, 516152836307031081372307480277628528799776768000000⟩,
  ⟨3, 5, 7, 3, 6, 6, -53200757731997807479185730011395700807853670400000⟩,
  ⟨3, 5, 8, 3, 7, 6, -112450279493898831691249855454815189160951808000000⟩,
  ⟨3, 5, 2, 4, 0, 6, 12264766183689880714164957617859200195408324198400000⟩,
  ⟨3, 5, 3, 4, 1, 6, -10646527148506188069910508392794407928325157683200000⟩,
  ⟨3, 5, 4, 4, 2, 6, -24295389006626143727945053255006858923884308070400000⟩,
  ⟨3, 5, 5, 4, 3, 6, -217113944034584946621345069021886002279481344000000⟩,
  ⟨3, 5, 6, 4, 4, 6, -238534512735550485166461140549514991333539840000000⟩,
  ⟨3, 5, 7, 4, 5, 6, -183165422049646144379090126412847976030404608000000⟩,
  ⟨3, 5, 8, 4, 6, 6, 143434636560451374646274793580775216354898739200000⟩,
  ⟨3, 5, 3, 5, 0, 6, 12787967729373278334365101173157951490115816652800000⟩,
  ⟨3, 5, 4, 5, 1, 6, 23423787391556655242093999770242363557153656012800000⟩,
  ⟨3, 5, 5, 5, 2, 6, -16863394262707143176017493149766003237830262784000000⟩,
  ⟨3, 5, 6, 5, 3, 6, -88359391854686698045048916145285317340954624000000⟩,
  ⟨3, 5, 7, 5, 4, 6, 116064916185493782600934512947310844666970112000000⟩,
  ⟨3, 5, 8, 5, 5, 6, 47945864393473145779859290346994523248682598400000⟩,
  ⟨3, 5, 4, 6, 0, 6, 73082769639763171538503191303678851362714130841600000⟩,
  ⟨3, 5, 5, 6, 1, 6, 21544158926671765780600764209506728850741002240000000⟩,
  ⟨3, 5, 6, 6, 2, 6, -6331213081077159870191331749434335891139067904000000⟩,
  ⟨3, 5, 7, 6, 3, 6, 348022791760447436499756304663062090377016115200000⟩,
  ⟨3, 5, 8, 6, 4, 6, -71422709767055779295816531953618840061372006400000⟩,
  ⟨3, 5, 5, 7, 0, 6, 93995665288022048354520476052984548239073083392000000⟩,
  ⟨3, 5, 6, 7, 1, 6, 12551339255644340490398127627966033227774164992000000⟩,
  ⟨3, 5, 7, 7, 2, 6, -618022965030550905534400085862316436215352524800000⟩,
  ⟨3, 5, 8, 7, 3, 6, -342075392378236682875991381637167066971216281600000⟩
]

def collectedFourData_10_2_30 : List CollectedFourTerm := [
  ⟨3, 6, 1, 0, 3, 7, -1056067462920454296776439542620830497162605363200000⟩,
  ⟨3, 6, 2, 0, 4, 7, -1975729215636425295638673423240250652745321676800000⟩,
  ⟨3, 6, 3, 0, 5, 7, 6790135320014375893016800314703814769896325120000000⟩,
  ⟨3, 6, 4, 0, 6, 7, 2375564164978408984747488104870870972538814464000000⟩,
  ⟨3, 6, 5, 0, 7, 7, 7677379529340609782348365322049305104613376000000⟩,
  ⟨3, 6, 6, 0, 8, 7, 94592935320934861551168209058788456365503283200000⟩,
  ⟨3, 6, 1, 1, 2, 7, -309921981073397740069563742567598782892998656000000⟩,
  ⟨3, 6, 2, 1, 3, 7, 1179600202418985577812385559759283212369736499200000⟩,
  ⟨3, 6, 3, 1, 4, 7, -6495504995445102427751497020744193470500752588800000⟩,
  ⟨3, 6, 4, 1, 5, 7, -3681223824657272158025853981358248488005219123200000⟩,
  ⟨3, 6, 5, 1, 6, 7, -1266708067699983105943131892364927337435758592000000⟩,
  ⟨3, 6, 6, 1, 7, 7, -316359138057502210189375625949167094488629248000000⟩,
  ⟨3, 6, 7, 1, 8, 7, -99121932362145562654324015579054827359541657600000⟩,
  ⟨3, 6, 1, 2, 1, 7, -1135316185372738929884725024547862681926133350400000⟩,
  ⟨3, 6, 2, 2, 2, 7, 287994169671169700210701998798767404557847756800000⟩,
  ⟨3, 6, 3, 2, 3, 7, 4505792374411591661955233930378600899381769011200000⟩,
  ⟨3, 6, 4, 2, 4, 7, 981485453223172601005033096053938065595223244800000⟩,
  ⟨3, 6, 5, 2, 5, 7, 221574895885807006481104418310312330094706688000000⟩,
  ⟨3, 6, 6, 2, 6, 7, 21838150462952758629482011805595004949653094400000⟩,
  ⟨3, 6, 7, 2, 7, 7, 5852272422268454848943545384940987253522432000000⟩,
  ⟨3, 6, 8, 2, 8, 7, 13515299228584414574253687589435813267714867200000⟩,
  ⟨3, 6, 1, 3, 0, 7, -996398069582047672464239983158272491387040563200000⟩,
  ⟨3, 6, 2, 3, 1, 7, 1650513133432715052439363143210387443369902080000000⟩,
  ⟨3, 6, 3, 3, 2, 7, -2971176951318794031703599603284167372712391475200000⟩,
  ⟨3, 6, 4, 3, 3, 7, -1251868248633506547659628147361512117843787776000000⟩,
  ⟨3, 6, 5, 3, 4, 7, -299892372182262118132883737054835500010962944000000⟩,
  ⟨3, 6, 6, 3, 5, 7, -53200757731997807479185730011395700807853670400000⟩,
  ⟨3, 6, 7, 3, 6, 7, 4569577755801128667621554815824698180999577600000⟩,
  ⟨3, 6, 8, 3, 7, 7, 8278887923216003313337632060650831443132416000000⟩,
  ⟨3, 6, 2, 4, 0, 7, -6320752386507774364683662434041127886166530457600000⟩,
  ⟨3, 6, 3, 4, 1, 7, 2743389514079376359488165309877658616617920102400000⟩,
  ⟨3, 6, 4, 4, 2, 7, 4173612328323695461865476563464150602759746355200000⟩,
  ⟨3, 6, 5, 4, 3, 7, 27972883040479043120862262649583991630331904000000⟩,
  ⟨3, 6, 6, 4, 4, 7, 24586161171873230396660627757941723498545152000000⟩,
  ⟨3, 6, 7, 4, 5, 7, 15732645058297326652237148275188890024804352000000⟩,
  ⟨3, 6, 8, 4, 6, 7, -10560038496441674686508011843293120108586598400000⟩,
  ⟨3, 6, 3, 5, 0, 7, -3295194393983253458909048224320325233965373849600000⟩,
  ⟨3, 6, 4, 5, 1, 7, -4023883207088026647055054207621909884296390246400000⟩,
  ⟨3, 6, 5, 5, 2, 7, 2172673696633001328682770613004859756137938944000000⟩,
  ⟨3, 6, 6, 5, 3, 7, 9107354002045252143036838364605440503001907200000⟩,
  ⟨3, 6, 7, 5, 4, 7, -9969174911040092851826789701496644281827328000000⟩,
  ⟨3, 6, 8, 5, 5, 7, -3529901743968662495363792865032913422175436800000⟩,
  ⟨3, 6, 4, 6, 0, 7, -12554610600117067412325393375583261009736682700800000⟩,
  ⟨3, 6, 5, 6, 1, 7, -2775741744921196501763452347712404761440419840000000⟩,
  ⟨3, 6, 6, 6, 2, 7, 652568986515618821352946288198366845469930291200000⟩,
  ⟨3, 6, 7, 6, 3, 7, -29892754831644931929523420727688803017084108800000⟩,
  ⟨3, 6, 8, 6, 4, 7, 5258329387842221673222231026630913208143052800000⟩,
  ⟨3, 6, 5, 7, 0, 7, -12110367959577115963415515632814972185159401472000000⟩,
  ⟨3, 6, 6, 7, 1, 7, -1293688055129558196187375608765212587183413657600000⟩,
  ⟨3, 6, 7, 7, 2, 7, 53083905454964894999386167422932374007264051200000⟩,
  ⟨3, 6, 8, 7, 3, 7, 25184497962436938192784113834364333072790323200000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1008
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1008. -/
namespace LaughlinFock
def collectedFourData_10_2_31 : List CollectedFourTerm := [
  ⟨3, 7, 0, 0, 2, 8, -6346259885375588231536913599774296931427155968000000⟩,
  ⟨3, 7, 1, 0, 3, 8, -13393239468661779258381002264152076487474806784000000⟩,
  ⟨3, 7, 2, 0, 4, 8, -12528278466734227974553615178902043933181739008000000⟩,
  ⟨3, 7, 3, 0, 5, 8, 28704576667251827346664996987791300503588044800000000⟩,
  ⟨3, 7, 4, 0, 6, 8, 7531834104315144930107921373998262240852049920000000⟩,
  ⟨3, 7, 5, 0, 7, 8, 19473184458104205458696452346581326678196224000000⟩,
  ⟨3, 7, 6, 0, 8, 8, 199940799124929620426757268322946388133412864000000⟩,
  ⟨3, 7, 0, 1, 1, 8, 46757423938874280297367366027109775636468596736000000⟩,
  ⟨3, 7, 1, 1, 2, 8, -3930486881623331386512110997856145659102494720000000⟩,
  ⟨3, 7, 2, 1, 3, 8, 7479952059402372551700281757022980806962839552000000⟩,
  ⟨3, 7, 3, 1, 4, 8, -27459058228883194883349148483001095505578033152000000⟩,
  ⟨3, 7, 4, 1, 5, 8, -11671487370000412865373903394800271728360554496000000⟩,
  ⟨3, 7, 5, 1, 6, 8, -3212924379030808657486144242230785538531524608000000⟩,
  ⟨3, 7, 6, 1, 7, 8, -668687346037902789081416233850869289802792960000000⟩,
  ⟨3, 7, 7, 1, 8, 8, -179583194030786588919848197193693646569865216000000⟩,
  ⟨3, 7, 0, 2, 0, 8, 7518197598960423538521648151082881327262859264000000⟩,
  ⟨3, 7, 1, 2, 1, 8, -14398286167528694924470215214113118235758952448000000⟩,
  ⟨3, 7, 2, 2, 2, 8, 1826197196397726467516140370431048669156343808000000⟩,
  ⟨3, 7, 3, 2, 3, 8, 19047759221644253632280082136761641530030030848000000⟩,
  ⟨3, 7, 4, 2, 4, 8, 3111844217242048757644887788118327892371308544000000⟩,
  ⟨3, 7, 5, 2, 5, 8, 562010618646612454133639354057229952836698112000000⟩,
  ⟨3, 7, 6, 2, 6, 8, 46159232083866723763755416131513220792844288000000⟩,
  ⟨3, 7, 7, 2, 7, 8, 10602797472606781878529011528890198387589120000000⟩,
  ⟨3, 7, 8, 2, 8, 8, 21425435094657074260896533726462641761681408000000⟩,
  ⟨3, 7, 1, 3, 0, 8, -12636501379486081293238912809518887503642230784000000⟩,
  ⟨3, 7, 2, 3, 1, 8, 10466053741067072402427233258596778120105164800000000⟩,
  ⟨3, 7, 3, 3, 2, 8, -12560335335249446488513593790740819810774417408000000⟩,
  ⟨3, 7, 4, 3, 3, 8, -3969105153281689174829487098594479991716577280000000⟩,
  ⟨3, 7, 5, 3, 4, 8, -760657911825963751768256215786874118346899456000000⟩,
  ⟨3, 7, 6, 3, 5, 8, -112450279493898831691249855454815189160951808000000⟩,
  ⟨3, 7, 7, 3, 6, 8, 8278887923216003313337632060650831443132416000000⟩,
  ⟨3, 7, 8, 3, 7, 8, 13124295130636433552741917746523149686538240000000⟩,
  ⟨3, 7, 2, 4, 0, 8, -40080465172417926633919850614084711440508256256000000⟩,
  ⟨3, 7, 3, 4, 1, 8, 11597388111384424121596298971645076121002704896000000⟩,
  ⟨3, 7, 4, 4, 2, 8, 13232627489539628266977590202670825544620179456000000⟩,
  ⟨3, 7, 5, 4, 3, 8, 70951437165567337541730451403887810493546496000000⟩,
  ⟨3, 7, 6, 4, 4, 8, 51967693945011909544795639906479245403095040000000⟩,
  ⟨3, 7, 7, 4, 5, 8, 28503466213706375177801674519366863232696320000000⟩,
  ⟨3, 7, 8, 4, 6, 8, -16740540891915483409406858839146935957323776000000⟩,
  ⟨3, 7, 3, 5, 0, 8, -13930084697544800193908803153443996391843037184000000⟩,
  ⟨3, 7, 4, 5, 1, 8, -12757904508633660136579060891601931088787668992000000⟩,
  ⟨3, 7, 5, 5, 2, 8, 5510848525869265248069892136651500015589523456000000⟩,
  ⟨3, 7, 6, 5, 3, 8, 19250186400332093712686980542581455762489344000000⟩,
  ⟨3, 7, 7, 5, 4, 8, -18061555396592254524788064406095639588372480000000⟩,
  ⟨3, 7, 8, 5, 5, 8, -5595856919391255338378218998593783334961152000000⟩,
  ⟨3, 7, 4, 6, 0, 8, -39804963249737178190417870975494147261515956224000000⟩,
  ⟨3, 7, 5, 6, 1, 8, -7040492240918682745617820139997388731486044160000000⟩,
  ⟨3, 7, 6, 6, 2, 8, 1379333078156441370989620877334879655925121024000000⟩,
  ⟨3, 7, 7, 6, 3, 8, -54157906964857983342485995192003942215057408000000⟩,
  ⟨3, 7, 8, 6, 4, 8, 8335886102119364244759777178007886618427392000000⟩,
  ⟨3, 7, 5, 7, 0, 8, -30717177421162978455077341139072206149651529728000000⟩,
  ⟨3, 7, 6, 7, 1, 8, -2734464499736633463176792975596422309454282752000000⟩,
  ⟨3, 7, 7, 7, 2, 8, 96174247878883295640483161640221122800648192000000⟩,
  ⟨3, 7, 8, 7, 3, 8, 39924297446889173189344267644774167240245248000000⟩
]

def collectedFourData_10_2_32 : List CollectedFourTerm := [
  ⟨4, 0, 6, 0, 8, 2, -21807212599951052825734733367044666910485721907200000⟩,
  ⟨4, 0, 6, 1, 7, 2, 72932623965527607973773887452834978327437508608000000⟩,
  ⟨4, 0, 7, 1, 8, 2, 137107895743302149285959516201221122400313776537600000⟩,
  ⟨4, 0, 6, 2, 6, 2, -5034511174852330869680865558614600236371699302400000⟩,
  ⟨4, 0, 7, 2, 7, 2, -8095007209930237217221392079788720426458284032000000⟩,
  ⟨4, 0, 8, 2, 8, 2, -65431430531512353332190193899467626233415807795200000⟩,
  ⟨4, 0, 6, 3, 5, 2, 12264766183689880714164957617859200195408324198400000⟩,
  ⟨4, 0, 7, 3, 6, 2, -6320752386507774364683662434041127886166530457600000⟩,
  ⟨4, 0, 8, 3, 7, 2, -40080465172417926633919850614084711440508256256000000⟩,
  ⟨4, 0, 6, 4, 4, 2, -5668030512771727238500167013830841238701473792000000⟩,
  ⟨4, 0, 7, 4, 5, 2, -21761781747136193148696195858015019098232061952000000⟩,
  ⟨4, 0, 8, 4, 6, 2, 51124167774892115774546958210176962713180595814400000⟩,
  ⟨4, 0, 6, 5, 3, 2, -2099586023753100791432332574423535425076540211200000⟩,
  ⟨4, 0, 7, 5, 4, 2, 13789608028985786627551222770303483863239753728000000⟩,
  ⟨4, 0, 8, 5, 5, 2, 17089264309817368262656773178812068713210891468800000⟩,
  ⟨4, 0, 6, 6, 2, 2, -150441579773359858997923650164743415877216711475200000⟩,
  ⟨4, 0, 7, 6, 3, 2, 41348393995822513934104474768657570085825465548800000⟩,
  ⟨4, 0, 8, 6, 4, 2, -25457077067500848315484351409513753509379230924800000⟩,
  ⟨4, 0, 6, 7, 1, 2, 298243524852154438348833444127604187384795208089600000⟩,
  ⟨4, 0, 7, 7, 2, 2, -73426964157391381562786290654592067299779490611200000⟩,
  ⟨4, 0, 8, 7, 3, 2, -121925360366054040628380472646757481384143696691200000⟩
]

def collectedFourData_10_2_33 : List CollectedFourTerm := [
  ⟨4, 1, 5, 0, 7, 3, 307279193278667007286334833065465989658417561600000⟩,
  ⟨4, 1, 6, 0, 8, 3, 18929923122984146444146871436095414619923388825600000⟩,
  ⟨4, 1, 5, 1, 6, 3, -50698683277920498615825062644925273980773020467200000⟩,
  ⟨4, 1, 6, 1, 7, 3, -63309740229159210037588856827844394934163472384000000⟩,
  ⟨4, 1, 7, 1, 8, 3, -59508795864645730909777474315481302192559122022400000⟩,
  ⟨4, 1, 5, 2, 5, 3, 8868306561945242900557905889613422876081048780800000⟩,
  ⟨4, 1, 6, 2, 6, 3, 4370247186106358709361848213204620932478612275200000⟩,
  ⟨4, 1, 7, 2, 7, 3, 3513467470031583189941530148861942892664455168000000⟩,
  ⟨4, 1, 8, 2, 8, 3, 18932756675669569854236658760250672207566680883200000⟩,
  ⟨4, 1, 5, 3, 4, 3, -12002882733935369989029388034808944175161435750400000⟩,
  ⟨4, 1, 6, 3, 5, 3, -10646527148506188069910508392794407928325157683200000⟩,
  ⟨4, 1, 7, 3, 6, 3, 2743389514079376359488165309877658616617920102400000⟩,
  ⟨4, 1, 8, 3, 7, 3, 11597388111384424121596298971645076121002704896000000⟩,
  ⟨4, 1, 5, 4, 3, 3, 1119585778130099843529893125866481200719619686400000⟩,
  ⟨4, 1, 6, 4, 4, 3, 4920178650697340231197347571168827036785442816000000⟩,
  ⟨4, 1, 7, 4, 5, 3, 9445243256200758001244612616101450877656629248000000⟩,
  ⟨4, 1, 8, 4, 6, 3, -14792912532486666593121900814374929584483624550400000⟩,
  ⟨4, 1, 5, 5, 2, 3, 86959022698791585102235495264099589703776757350400000⟩,
  ⟨4, 1, 6, 5, 3, 3, 1822562229701349969021486940625465121017797017600000⟩,
  ⟨4, 1, 7, 5, 4, 3, -5985089077486496109876132344395178044997763072000000⟩,
  ⟨4, 1, 8, 5, 5, 3, -4944823616352900526220548332708078457906318540800000⟩,
  ⟨4, 1, 5, 6, 1, 3, -111096199018125198971903169833411169958068486144000000⟩,
  ⟨4, 1, 6, 6, 2, 3, 130592001456269609152623872697350039696016251289600000⟩,
  ⟨4, 1, 7, 6, 3, 3, -17946399981479895875968105293568578606010151731200000⟩,
  ⟨4, 1, 8, 6, 4, 3, 7366072266456701278500952032234369013856914636800000⟩,
  ⟨4, 1, 5, 7, 0, 3, -484704980743121153694800770053088705280774189875200000⟩,
  ⟨4, 1, 6, 7, 1, 3, -258892647169027338322210017620962740761768283340800000⟩,
  ⟨4, 1, 7, 7, 2, 3, 31869428068414646529096234640589008703480188108800000⟩,
  ⟨4, 1, 8, 7, 3, 3, 35279423996271791009659744836052034912653620019200000⟩
]

def collectedFourData_10_2_34 : List CollectedFourTerm := [
  ⟨4, 2, 4, 0, 6, 4, 108485777193429676188589311842835132715071071846400000⟩,
  ⟨4, 2, 5, 0, 7, 4, 1402423049359331147498463049040967195762779750400000⟩,
  ⟨4, 2, 6, 0, 8, 4, 43198109554715870092484183856652589554774258483200000⟩,
  ⟨4, 2, 4, 1, 5, 4, -168111825194392745913044085224644762110565621432320000⟩,
  ⟨4, 2, 5, 1, 6, 4, -231388924327992937112523559880877537249383468236800000⟩,
  ⟨4, 2, 6, 1, 7, 4, -144472910773696467455277399364561274253499957248000000⟩,
  ⟨4, 2, 7, 1, 8, 4, -90532767144344128877418667361985412666674590515200000⟩,
  ⟨4, 2, 4, 2, 4, 4, 44821863272183682295723978077855548154512387604480000⟩,
  ⟨4, 2, 5, 2, 5, 4, 40474974561579161859658225139561508047458349875200000⟩,
  ⟨4, 2, 6, 2, 6, 4, 9972909847552017740099633134409635800824571494400000⟩,
  ⟨4, 2, 7, 2, 7, 4, 5345158269662978824823498368975732201293348864000000⟩,
  ⟨4, 2, 8, 2, 8, 4, 21602287862842190404973177669793894112842429235200000⟩,
  ⟨4, 2, 4, 3, 3, 4, -57169535514532382388699303361279473823994452377600000⟩,
  ⟨4, 2, 5, 3, 4, 4, -54781188486011147276238865040469152865564858777600000⟩,
  ⟨4, 2, 6, 3, 5, 4, -24295389006626143727945053255006858923884308070400000⟩,
  ⟨4, 2, 7, 3, 6, 4, 4173612328323695461865476563464150602759746355200000⟩,
  ⟨4, 2, 8, 3, 7, 4, 13232627489539628266977590202670825544620179456000000⟩,
  ⟨4, 2, 4, 4, 2, 4, 190597915146775626407564456666284006726981669355520000⟩,
  ⟨4, 2, 5, 4, 3, 4, 5109792447159361078222591211356197370872830361600000⟩,
  ⟨4, 2, 6, 4, 4, 4, 11227854175674657966368380471544039330285617152000000⟩,
  ⟨4, 2, 7, 4, 5, 4, 14369371719102933044159855432434919267006152704000000⟩,
  ⟨4, 2, 8, 4, 6, 4, -16878722963111306311857752180993474530654971494400000⟩,
  ⟨4, 2, 4, 5, 1, 4, -183760179367961830155722005432200762121547038064640000⟩,
  ⟨4, 2, 5, 5, 2, 4, 396881209174318841684579885359835411236790049177600000⟩,
  ⟨4, 2, 6, 5, 3, 4, 4159089414015264873917598716324206500241421107200000⟩,
  ⟨4, 2, 7, 5, 4, 4, -9105320783547467614610176747633383356976070656000000⟩,
  ⟨4, 2, 8, 5, 5, 4, -5642047009916370044724016182614306810881690828800000⟩,
  ⟨4, 2, 4, 6, 0, 4, -573336097754677790685317843829627782169849055150080000⟩,
  ⟨4, 2, 5, 6, 1, 4, -507043345619350220024867097272538377499690663936000000⟩,
  ⟨4, 2, 6, 6, 2, 4, 298011119708564363218684935438960419465017373491200000⟩,
  ⟨4, 2, 7, 6, 3, 4, -27302472298348758100143103538981071231016081817600000⟩,
  ⟨4, 2, 8, 6, 4, 4, 8404693317745210702793938429100889044496993484800000⟩,
  ⟨4, 2, 5, 7, 0, 4, -2212194811761817349415141820919763225037691997388800000⟩,
  ⟨4, 2, 6, 7, 1, 4, -590793362585776339251730669249075674290153167257600000⟩,
  ⟨4, 2, 7, 7, 2, 4, 48484051280481820024814146996563356959556134502400000⟩,
  ⟨4, 2, 8, 7, 3, 4, 40253846064694795678591343762695309024864449331200000⟩
]

def collectedFourData_10_2_35 : List CollectedFourTerm := [
  ⟨4, 3, 3, 0, 5, 5, 2771075305512380725105156172883584572792504320000000⟩,
  ⟨4, 3, 4, 0, 6, 5, 2908425333510674960184172401592977044759642112000000⟩,
  ⟨4, 3, 5, 0, 7, 5, 18798974531856887338624128846105203982729216000000⟩,
  ⟨4, 3, 6, 0, 8, 5, 386036705882935892519398054672560735966461952000000⟩,
  ⟨4, 3, 3, 1, 4, 5, -2650835755313360124464287093961175662735445196800000⟩,
  ⟨4, 3, 4, 1, 5, 5, -4506956615947091871627544672152804197700049305600000⟩,
  ⟨4, 3, 5, 1, 6, 5, -3101684971152501170007341620083981060377935872000000⟩,
  ⟨4, 3, 6, 1, 7, 5, -1291071464452744277068754683637619913685729280000000⟩,
  ⟨4, 3, 7, 1, 8, 5, -606779525130646114785523263196767388491055104000000⟩,
  ⟨4, 3, 3, 2, 3, 5, 1838827857184961364158961747107101587499332403200000⟩,
  ⟨4, 3, 4, 2, 4, 5, 1201641782070082037201196081007570732615886438400000⟩,
  ⟨4, 3, 5, 2, 5, 5, 542552417623397221682650614335263527149764608000000⟩,
  ⟨4, 3, 6, 2, 6, 5, 89122170050985129867395160486309644136873984000000⟩,
  ⟨4, 3, 7, 2, 7, 5, 35824958177221358782678822022134300441313280000000⟩,
  ⟨4, 3, 8, 2, 8, 5, 115828347102232959223871795049822117076087603200000⟩,
  ⟨4, 3, 3, 3, 2, 5, -1212546538481892829943273603613376671244301107200000⟩,
  ⟨4, 3, 4, 3, 3, 5, -1532673956873070961920893511862140425950199808000000⟩,
  ⟨4, 3, 5, 3, 4, 5, -734322049002141385751844720595458671618555904000000⟩,
  ⟨4, 3, 6, 3, 5, 5, -217113944034584946621345069021886002279481344000000⟩,
  ⟨4, 3, 7, 3, 6, 5, 27972883040479043120862262649583991630331904000000⟩,
  ⟨4, 3, 8, 3, 7, 5, 70951437165567337541730451403887810493546496000000⟩,
  ⟨4, 3, 3, 4, 1, 5, 1119585778130099843529893125866481200719619686400000⟩,
  ⟨4, 3, 4, 4, 2, 5, 5109792447159361078222591211356197370872830361600000⟩,
  ⟨4, 3, 5, 4, 3, 5, 68494922499388520502834147720360846912651264000000⟩,
  ⟨4, 3, 6, 4, 4, 5, 100336887071907428784703233986747255457054720000000⟩,
  ⟨4, 3, 7, 4, 5, 5, 96308119404342320901444237604580610885550080000000⟩,
  ⟨4, 3, 8, 4, 6, 5, -90501274421794716782024550844317215448524390400000⟩,
  ⟨4, 3, 3, 5, 0, 5, -1344779062814096602798194662321631454629042585600000⟩,
  ⟨4, 3, 4, 5, 1, 5, -4926477689433139732840311615290600580522914611200000⟩,
  ⟨4, 3, 5, 5, 2, 5, 5320049286731971354124091784582756245285371904000000⟩,
  ⟨4, 3, 6, 5, 3, 5, 37167394439457973725341774325765887955566592000000⟩,
  ⟨4, 3, 7, 5, 4, 5, -61026768489184465803604170753717832903557120000000⟩,
  ⟨4, 3, 8, 5, 5, 5, -30251841081879158885023605542694555600342220800000⟩,
  ⟨4, 3, 4, 6, 0, 5, -15370726693073351058269916762997952827156227686400000⟩,
  ⟨4, 3, 5, 6, 1, 5, -6796732943886033052530347408079169663732285440000000⟩,
  ⟨4, 3, 6, 6, 2, 5, 2663154294357781018440842827712631040043384832000000⟩,
  ⟨4, 3, 7, 6, 3, 5, -182989890827827710924229683321122167562698752000000⟩,
  ⟨4, 3, 8, 6, 4, 5, 45064751524310424948139200270404098045299916800000⟩,
  ⟨4, 3, 5, 7, 0, 5, -29653672581047872608521443100361814189855997952000000⟩,
  ⟨4, 3, 6, 7, 1, 5, -5279581118271834746629710021642370464387956736000000⟩,
  ⟨4, 3, 7, 7, 2, 5, 324955599396130469932232957223337224881307648000000⟩,
  ⟨4, 3, 8, 7, 3, 5, 215835307990747143245604433558096873992172339200000⟩
]

def collectedFourData_10_2_36 : List CollectedFourTerm := [
  ⟨4, 4, 2, 0, 4, 6, -1771702606655818610071521634126747725050413056000000⟩,
  ⟨4, 4, 3, 0, 5, 6, 12177883842386826448348679125621584513780940800000000⟩,
  ⟨4, 4, 4, 0, 6, 6, 6390744020072593708213499957719027688291696640000000⟩,
  ⟨4, 4, 5, 0, 7, 6, 27538254163108621741278588834126736580935680000000⟩,
  ⟨4, 4, 6, 0, 8, 6, 424123277504253009379722347968894574757150720000000⟩,
  ⟨4, 4, 2, 1, 3, 6, 1057787037260693434330640643814954083878436864000000⟩,
  ⟨4, 4, 3, 1, 4, 6, -11649474068508896518966309307256628030778376192000000⟩,
  ⟨4, 4, 4, 1, 5, 6, -9903230352942727219162064125784200613128568832000000⟩,
  ⟨4, 4, 5, 1, 6, 6, -4543598318341615439496998495040463616669122560000000⟩,
  ⟨4, 4, 6, 1, 7, 6, -1418449211308841384208710419316467460525260800000000⟩,
  ⟨4, 4, 7, 1, 8, 6, -533315753655662061920271929457424537592266752000000⟩,
  ⟨4, 4, 2, 2, 2, 6, 258254024422942018980440041131875679816646656000000⟩,
  ⟨4, 4, 3, 2, 3, 6, 8080990078616065720760445451730517034750967808000000⟩,
  ⟨4, 4, 4, 2, 4, 6, 2640392704791974521584696349993998019196878848000000⟩,
  ⟨4, 4, 5, 2, 5, 6, 794774541983825928959939454369838913122467840000000⟩,
  ⟨4, 4, 6, 2, 6, 6, 97915007263007590118882286742878491498250240000000⟩,
  ⟨4, 4, 7, 2, 7, 6, 31487572962936831597800861723745019641200640000000⟩,
  ⟨4, 4, 8, 2, 8, 6, 84837352601035478952791444393806161896275968000000⟩,
  ⟨4, 4, 2, 3, 1, 6, 1480070445726769263847302663955308120480153600000000⟩,
  ⟨4, 4, 3, 3, 2, 6, -5328707909794747260246710344798785020853485568000000⟩,
  ⟨4, 4, 4, 3, 3, 6, -3367776649361119915888724863925852835686645760000000⟩,
  ⟨4, 4, 5, 3, 4, 6, -1075694165590117987962456346139624260679761920000000⟩,
  ⟨4, 4, 6, 3, 5, 6, -238534512735550485166461140549514991333539840000000⟩,
  ⟨4, 4, 7, 3, 6, 6, 24586161171873230396660627757941723498545152000000⟩,
  ⟨4, 4, 8, 3, 7, 6, 51967693945011909544795639906479245403095040000000⟩,
  ⟨4, 4, 2, 4, 0, 6, -5668030512771727238500167013830841238701473792000000⟩,
  ⟨4, 4, 3, 4, 1, 6, 4920178650697340231197347571168827036785442816000000⟩,
  ⟨4, 4, 4, 4, 2, 6, 11227854175674657966368380471544039330285617152000000⟩,
  ⟨4, 4, 5, 4, 3, 6, 100336887071907428784703233986747255457054720000000⟩,
  ⟨4, 4, 6, 4, 4, 6, 110236173791246135779543965499723705692979200000000⟩,
  ⟨4, 4, 7, 4, 5, 6, 84647940736344707590186976831144660607959040000000⟩,
  ⟨4, 4, 8, 4, 6, 6, -66286783167061666491005683184505010935300096000000⟩,
  ⟨4, 4, 3, 5, 0, 6, -5909822511155396779885305902427690324002340864000000⟩,
  ⟨4, 4, 4, 5, 1, 6, -10825052811571629508922222164456725113852657664000000⟩,
  ⟨4, 4, 5, 5, 2, 6, 7793237294407813646111580081746284094863441920000000⟩,
  ⟨4, 4, 6, 5, 3, 6, 40834347889023021834748987112355347426181120000000⟩,
  ⟨4, 4, 7, 5, 4, 6, -53638159631328043634667748121471932233154560000000⟩,
  ⟨4, 4, 8, 5, 5, 6, -22157668419705832507441289310430664476065792000000⟩,
  ⟨4, 4, 4, 6, 0, 6, -33774420325020928082688378411244854661934481408000000⟩,
  ⟨4, 4, 5, 6, 1, 6, -9956402620277349251237736389722645778871091200000000⟩,
  ⟨4, 4, 6, 6, 2, 6, 2925902409303705999093389108506954063958507520000000⟩,
  ⟨4, 4, 7, 6, 3, 6, -160835010899877989193858358265311510948478976000000⟩,
  ⟨4, 4, 8, 6, 4, 6, 33007241410183870013421684277669018397048832000000⟩,
  ⟨4, 4, 5, 7, 0, 6, -43439091372918630553794289021691732687805480960000000⟩,
  ⟨4, 4, 6, 7, 1, 6, -5800467192904827841951138277054691417218088960000000⟩,
  ⟨4, 4, 7, 7, 2, 6, 285612703163081409494016689707466278488244224000000⟩,
  ⟨4, 4, 8, 7, 3, 6, 158086483886387990900546654605912440840388608000000⟩
]

def collectedFourData_10_2_37 : List CollectedFourTerm := [
  ⟨4, 5, 1, 0, 3, 7, -3635945253508706422283668519252910982366756864000000⟩,
  ⟨4, 5, 2, 0, 4, 7, -6802257920101104807938540653022299818804903936000000⟩,
  ⟨4, 5, 3, 0, 5, 7, 23377824953733752983942284215108100719797862400000000⟩,
  ⟨4, 5, 4, 0, 6, 7, 8178853674908846623551228207399039826950881280000000⟩,
  ⟨4, 5, 5, 0, 7, 7, 26432526935254599898775755610782288073195520000000⟩,
  ⟨4, 5, 6, 0, 8, 7, 325674965162254240575675766407729498254475264000000⟩,
  ⟨4, 5, 1, 1, 2, 7, -1067033495119348819004506475999608320420741120000000⟩,
  ⟨4, 5, 2, 1, 3, 7, 4061257360550152182973637941454518568651587584000000⟩,
  ⟨4, 5, 3, 1, 4, 7, -22363439256067325126521447233241449338215858176000000⟩,
  ⟨4, 5, 4, 1, 5, 7, -12674122404407366194720119017534420432468312064000000⟩,
  ⟨4, 5, 5, 1, 6, 7, -4361161903045819357736641831321920675344547840000000⟩,
  ⟨4, 5, 6, 1, 7, 7, -1089196047422324186303973771685054536178728960000000⟩,
  ⟨4, 5, 7, 1, 8, 7, -341267894471530171234104218493176038085885952000000⟩,
  ⟨4, 5, 1, 2, 1, 7, -3908791474383818175760323114124293916179038208000000⟩,
  ⟨4, 5, 2, 2, 2, 7, 991538013450702357907356372594211468697665536000000⟩,
  ⟨4, 5, 3, 2, 3, 7, 15513037729362888614168266099960956828279373824000000⟩,
  ⟨4, 5, 4, 2, 4, 7, 3379166104754269913311812830351531364682039296000000⟩,
  ⟨4, 5, 5, 2, 5, 7, 762862429986036049573028518665267242084597760000000⟩,
  ⟨4, 5, 6, 2, 6, 7, 75186787122105312270347874829273174363865088000000⟩,
  ⟨4, 5, 7, 2, 7, 7, 20148847382479809152122540099630065663344640000000⟩,
  ⟨4, 5, 8, 2, 8, 7, 46531959183769305288549596805343073160658944000000⟩,
  ⟨4, 5, 1, 3, 0, 7, -3430508901091829460913447943136283776321060864000000⟩,
  ⟨4, 5, 2, 3, 1, 7, 5682568210900828032906898048251187493968281600000000⟩,
  ⟨4, 5, 3, 3, 2, 7, -10229494907084122912837389951328606012890415104000000⟩,
  ⟨4, 5, 4, 3, 3, 7, -4310069741235937324914552571314727235899883520000000⟩,
  ⟨4, 5, 5, 3, 4, 7, -1032502454136960290712375873641425922823290880000000⟩,
  ⟨4, 5, 6, 3, 5, 7, -183165422049646144379090126412847976030404608000000⟩,
  ⟨4, 5, 7, 3, 6, 7, 15732645058297326652237148275188890024804352000000⟩,
  ⟨4, 5, 8, 3, 7, 7, 28503466213706375177801674519366863232696320000000⟩,
  ⟨4, 5, 2, 4, 0, 7, -21761781747136193148696195858015019098232061952000000⟩,
  ⟨4, 5, 3, 4, 1, 7, 9445243256200758001244612616101450877656629248000000⟩,
  ⟨4, 5, 4, 4, 2, 7, 14369371719102933044159855432434919267006152704000000⟩,
  ⟨4, 5, 5, 4, 3, 7, 96308119404342320901444237604580610885550080000000⟩,
  ⟨4, 5, 6, 4, 4, 7, 84647940736344707590186976831144660607959040000000⟩,
  ⟨4, 5, 7, 4, 5, 7, 54166081366301926979833856408685825270743040000000⟩,
  ⟨4, 5, 8, 4, 6, 7, -36357262387221551843565098188788026906247168000000⟩,
  ⟨4, 5, 3, 5, 0, 7, -11345057808200231738200838283311919649932705792000000⟩,
  ⟨4, 5, 4, 5, 1, 7, -13853867826801058569410318358046063530111664128000000⟩,
  ⟨4, 5, 5, 5, 2, 7, 7480320047783731071836907343408346447090810880000000⟩,
  ⟨4, 5, 6, 5, 3, 7, 31355800380580587476091030212215690959519744000000⟩,
  ⟨4, 5, 7, 5, 4, 7, -34322972226561771425277547976408305300930560000000⟩,
  ⟨4, 5, 8, 5, 5, 7, -12153134096038041715526154141877160311259136000000⟩,
  ⟨4, 5, 4, 6, 0, 7, -43224394675422415144083347217627224976094396416000000⟩,
  ⟨4, 5, 5, 6, 1, 7, -9556629076046430295343885538556309255539916800000000⟩,
  ⟨4, 5, 6, 6, 2, 7, 2246736304655159627421490127851754386750439424000000⟩,
  ⟨4, 5, 7, 6, 3, 7, -102918065237850747672377499440842391553048576000000⟩,
  ⟨4, 5, 8, 6, 4, 7, 18103954955906410274378101328033375066259456000000⟩,
  ⟨4, 5, 5, 7, 0, 7, -41694907235471739317048848181171275062250045440000000⟩,
  ⟨4, 5, 6, 7, 1, 7, -4454051572199159316392453902462085483779325952000000⟩,
  ⟨4, 5, 7, 7, 2, 7, 182763110173788735503917671331780250906394624000000⟩,
  ⟨4, 5, 8, 7, 3, 7, 86707960469964331511701375520733121493336064000000⟩
]

def collectedFourData_10_2_38 : List CollectedFourTerm := [
  ⟨4, 6, 0, 0, 2, 8, 8094897445109575113615655379798753956628476723200000⟩,
  ⟨4, 6, 1, 0, 3, 8, 17083589691378446438109520648786630182449027481600000⟩,
  ⟨4, 6, 2, 0, 4, 8, 15980298819102992799792067528800151696445748019200000⟩,
  ⟨4, 6, 3, 0, 5, 8, -36613786470066224257618891272624285903507947520000000⟩,
  ⟨4, 6, 4, 0, 6, 8, -9607142750095791576871226295145568059741175808000000⟩,
  ⟨4, 6, 5, 0, 7, 8, -24838792291079655437195039757573275482954137600000⟩,
  ⟨4, 6, 6, 0, 8, 8, -255032143852043412508852775484354729034226073600000⟩,
  ⟨4, 6, 0, 1, 1, 8, -59640884303353467777668271020347856812859876966400000⟩,
  ⟨4, 6, 1, 1, 2, 8, 5013486492951336126059407185322366358758883328000000⟩,
  ⟨4, 6, 2, 1, 3, 8, -9540965215548353822258005074632795989857848524800000⟩,
  ⟨4, 6, 3, 1, 4, 8, 35025080018283339026284288262689024518394793164800000⟩,
  ⟨4, 6, 4, 1, 5, 8, 14887428973680215616813785868895130218303743590400000⟩,
  ⟨4, 6, 5, 1, 6, 8, 4098208049607398392544224081045669356051313459200000⟩,
  ⟨4, 6, 6, 1, 7, 8, 852936310013558294755742008229915173117231104000000⟩,
  ⟨4, 6, 7, 1, 8, 8, 229065239180383368555759970313315045907785318400000⟩,
  ⟨4, 6, 0, 2, 0, 8, -9589748865453510764463276763569677700236417433600000⟩,
  ⟨4, 6, 1, 2, 1, 8, 18365565233165152388627048051250512068540052275200000⟩,
  ⟨4, 6, 2, 2, 2, 8, -2329384438455176118142247530240371128689439539200000⟩,
  ⟨4, 6, 3, 2, 3, 8, -24296146114921524562690595455059510216459760435200000⟩,
  ⟨4, 6, 4, 2, 4, 8, -3969276433475407949252832701430117783762999705600000⟩,
  ⟨4, 6, 5, 2, 5, 8, -716866060195653086536853072747162220215717068800000⟩,
  ⟨4, 6, 6, 2, 6, 8, -58877867691010708870932805851388206279504691200000⟩,
  ⟨4, 6, 7, 2, 7, 8, -13524274095645444980934231539872998661029888000000⟩,
  ⟨4, 6, 8, 2, 8, 8, -27328962718304458673041294550930285541929779200000⟩,
  ⟨4, 6, 1, 3, 0, 8, 16118341287542724331492918928962158728694045081600000⟩,
  ⟨4, 6, 2, 3, 1, 8, -13349852230945834894866290996639052544365035520000000⟩,
  ⟨4, 6, 3, 3, 2, 8, 16021188582164862462490993362599500295217296179200000⟩,
  ⟨4, 6, 4, 3, 3, 8, 5062745576920174701729523952667660351776489472000000⟩,
  ⟨4, 6, 5, 3, 4, 8, 970248287693305613411071550627317678095099494400000⟩,
  ⟨4, 6, 6, 3, 5, 8, 143434636560451374646274793580775216354898739200000⟩,
  ⟨4, 6, 7, 3, 6, 8, -10560038496441674686508011843293120108586598400000⟩,
  ⟨4, 6, 8, 3, 7, 8, -16740540891915483409406858839146935957323776000000⟩,
  ⟨4, 6, 2, 4, 0, 8, 51124167774892115774546958210176962713180595814400000⟩,
  ⟨4, 6, 3, 4, 1, 8, -14792912532486666593121900814374929584483624550400000⟩,
  ⟨4, 6, 4, 4, 2, 8, -16878722963111306311857752180993474530654971494400000⟩,
  ⟨4, 6, 5, 4, 3, 8, -90501274421794716782024550844317215448524390400000⟩,
  ⟨4, 6, 6, 4, 4, 8, -66286783167061666491005683184505010935300096000000⟩,
  ⟨4, 6, 7, 4, 5, 8, -36357262387221551843565098188788026906247168000000⟩,
  ⟨4, 6, 8, 4, 6, 8, 21353200805406191389971973067508457178293862400000⟩,
  ⟨4, 6, 3, 5, 0, 8, 17768356333494496647690017014406777797315500441600000⟩,
  ⟨4, 6, 4, 5, 1, 8, 16273195626588891883960193015645179148575231180800000⟩,
  ⟨4, 6, 5, 5, 2, 8, -7029298273026028433226970796760621858280597094400000⟩,
  ⟨4, 6, 6, 5, 3, 8, -24554349731095046246475684266384025563273625600000⟩,
  ⟨4, 6, 7, 5, 4, 8, 23038205380069590551863933889953052284157952000000⟩,
  ⟨4, 6, 8, 5, 5, 8, 7137729733439393045582588236880593241820364800000⟩,
  ⟨4, 6, 4, 6, 0, 8, 50772754525149479431273175024892363206261578137600000⟩,
  ⟨4, 6, 5, 6, 1, 8, 8980417392716575309377252673497022522913193984000000⟩,
  ⟨4, 6, 6, 6, 2, 8, -1759392147815090014658484339907055436156213657600000⟩,
  ⟨4, 6, 7, 6, 3, 8, 69080483724370064343819754320767552626832179200000⟩,
  ⟨4, 6, 8, 6, 4, 8, -10632741855761068263699595785575338062171340800000⟩,
  ⟨4, 6, 5, 7, 0, 8, 39180935782435865853291529448767317270338941747200000⟩,
  ⟨4, 6, 6, 7, 1, 8, 3487914156126760501008969406544212284979072204800000⟩,
  ⟨4, 6, 7, 7, 2, 8, -122673935121084704384707583597476535232941260800000⟩,
  ⟨4, 6, 8, 7, 3, 8, -50924969862227928805617878372722546998194995200000⟩
]

def collectedFourData_10_2_39 : List CollectedFourTerm := [
  ⟨5, 0, 5, 0, 7, 3, -369085275671963326255728201275713876474095206400000⟩,
  ⟨5, 0, 6, 0, 8, 3, -22737484499835593683283523698955546754896258662400000⟩,
  ⟨5, 0, 5, 1, 6, 3, 60896207433306688720210886016270916878838058188800000⟩,
  ⟨5, 0, 6, 1, 7, 3, 76043850141225480056803974801691476847478439936000000⟩,
  ⟨5, 0, 7, 1, 8, 3, 71478384501910265321096495665327727577356933529600000⟩,
  ⟨5, 0, 5, 2, 5, 3, -10652076169669773569492804716704151665548407603200000⟩,
  ⟨5, 0, 6, 2, 6, 3, -5249277929390705111073732271404162625684950220800000⟩,
  ⟨5, 0, 7, 2, 7, 3, -4220165693305050707396542507548423213885161472000000⟩,
  ⟨5, 0, 8, 2, 8, 3, -22740887992805200935837992498588450083771829452800000⟩,
  ⟨5, 0, 5, 3, 4, 3, 14417140436499400374675637749994289814329465241600000⟩,
  ⟨5, 0, 6, 3, 5, 3, 12787967729373278334365101173157951490115816652800000⟩,
  ⟨5, 0, 7, 3, 6, 3, -3295194393983253458909048224320325233965373849600000⟩,
  ⟨5, 0, 8, 3, 7, 3, -13930084697544800193908803153443996391843037184000000⟩,
  ⟨5, 0, 5, 4, 3, 3, -1344779062814096602798194662321631454629042585600000⟩,
  ⟨5, 0, 6, 4, 4, 3, -5909822511155396779885305902427690324002340864000000⟩,
  ⟨5, 0, 7, 4, 5, 3, -11345057808200231738200838283311919649932705792000000⟩,
  ⟨5, 0, 8, 4, 6, 3, 17768356333494496647690017014406777797315500441600000⟩,
  ⟨5, 0, 5, 5, 2, 3, -104449945088996816281664427676957179164671711641600000⟩,
  ⟨5, 0, 6, 5, 3, 3, -2189152073074425324552927910550266499249366630400000⟩,
  ⟨5, 0, 7, 5, 4, 3, 7188928832164834560376158362075760789697855488000000⟩,
  ⟨5, 0, 8, 5, 5, 3, 5939424560828377485979443240715821564248142643200000⟩,
  ⟨5, 0, 5, 6, 1, 3, 133442068768796000201890350531238776308263550976000000⟩,
  ⟨5, 0, 6, 6, 2, 3, -156859253448798292455295568034532256615380706918400000⟩,
  ⟨5, 0, 7, 6, 3, 3, 21556135688226833768493053930650716589244861644800000⟩,
  ⟨5, 0, 8, 6, 4, 3, -8847682734636764095825027320511841966633464627200000⟩,
  ⟨5, 0, 5, 7, 0, 3, 582198454533525950489730126791099409316981820620800000⟩,
  ⟨5, 0, 6, 7, 1, 3, 310966268266555723599484108844519554176938881843200000⟩,
  ⟨5, 0, 7, 7, 2, 3, -38279639173197623669049149411113914769211601715200000⟩,
  ⟨5, 0, 8, 7, 3, 3, -42375521076701709561637230405631628368975547596800000⟩
]

def collectedFourData_10_2_40 : List CollectedFourTerm := [
  ⟨5, 1, 4, 0, 6, 4, -104593829688984557734121377876683942513433431244800000⟩,
  ⟨5, 1, 5, 0, 7, 4, -1352110860717326106768608889393263222469741772800000⟩,
  ⟨5, 1, 6, 0, 8, 4, -41648369312006841935982796921250035600418301542400000⟩,
  ⟨5, 1, 4, 1, 5, 4, 162080782089392464418257344545542629249761138442240000⟩,
  ⟨5, 1, 5, 1, 6, 4, 223087803481627156352270466424108990951144921497600000⟩,
  ⟨5, 1, 6, 1, 7, 4, 139289918135471959495836349328113928022981083136000000⟩,
  ⟨5, 1, 7, 1, 8, 4, 87284887226134161273898219308725530662520907366400000⟩,
  ⟨5, 1, 4, 2, 4, 4, -43213870561805416911088539360564349108164608655360000⟩,
  ⟨5, 1, 5, 2, 5, 4, -39022927294990946901001448890573894587521590886400000⟩,
  ⟨5, 1, 6, 2, 6, 4, -9615129845441409708812479529704121052242431180800000⟩,
  ⟨5, 1, 7, 2, 7, 4, -5153399719126098551480260400990778340040245248000000⟩,
  ⟨5, 1, 8, 2, 8, 4, -20827301753942510199116442400175012571540514406400000⟩,
  ⟨5, 1, 4, 3, 3, 4, 55118567757907909416370028630090146767787209523200000⟩,
  ⟨5, 1, 5, 3, 4, 4, 52815903124792558866515277260976661854036374323200000⟩,
  ⟨5, 1, 6, 3, 5, 4, 23423787391556655242093999770242363557153656012800000⟩,
  ⟨5, 1, 7, 3, 6, 4, -4023883207088026647055054207621909884296390246400000⟩,
  ⟨5, 1, 8, 3, 7, 4, -12757904508633660136579060891601931088787668992000000⟩,
  ⟨5, 1, 4, 4, 2, 4, -183760179367961830155722005432200762121547038064640000⟩,
  ⟨5, 1, 5, 4, 3, 4, -4926477689433139732840311615290600580522914611200000⟩,
  ⟨5, 1, 6, 4, 4, 4, -10825052811571629508922222164456725113852657664000000⟩,
  ⟨5, 1, 7, 4, 5, 4, -13853867826801058569410318358046063530111664128000000⟩,
  ⟨5, 1, 8, 4, 6, 4, 16273195626588891883960193015645179148575231180800000⟩,
  ⟨5, 1, 4, 5, 1, 4, 177167748636398238665080783067966474799670603284480000⟩,
  ⟨5, 1, 5, 5, 2, 4, -382643021721846954251949551717341176230768227123200000⟩,
  ⟨5, 1, 6, 5, 3, 4, -4009881305040947033226935220175988954948331110400000⟩,
  ⟨5, 1, 7, 5, 4, 4, 8778665701033609135937919559920892280561467392000000⟩,
  ⟨5, 1, 8, 5, 5, 4, 5439637520412008040872884650771011445741689241600000⟩,
  ⟨5, 1, 4, 6, 0, 4, 552767558241096625370707186652223351751602402754560000⟩,
  ⟨5, 1, 5, 6, 1, 4, 488853070961408701696516664144925706017520484352000000⟩,
  ⟨5, 1, 6, 6, 2, 4, -287319915168648994426613334145665641328901776998400000⟩,
  ⟨5, 1, 7, 6, 3, 4, 26322991008950981301798815417105948407405687603200000⟩,
  ⟨5, 1, 8, 6, 4, 4, -8103173376331119792328922816741958806419380633600000⟩,
  ⟨5, 1, 5, 7, 0, 4, 2132831910008975562387939671228271000407183563161600000⟩,
  ⟨5, 1, 6, 7, 1, 4, 569598540438180487557430519671925590295045157683200000⟩,
  ⟨5, 1, 7, 7, 2, 4, -46744676891800308857116333774229142516087442636800000⟩,
  ⟨5, 1, 8, 7, 3, 4, -38809731824203414837098986178620131725906699878400000⟩
]

def collectedFourData_10_2_41 : List CollectedFourTerm := [
  ⟨5, 2, 3, 0, 5, 5, 215231387446322466677461574296143940659204587520000000⟩,
  ⟨5, 2, 4, 0, 6, 5, 225899461689219301099118220870543508151029727232000000⟩,
  ⟨5, 2, 5, 0, 7, 5, 1460129705970403396874579179994955932422373376000000⟩,
  ⟨5, 2, 6, 0, 8, 5, 29983745171814850222644504665010286365845225472000000⟩,
  ⟨5, 2, 3, 1, 4, 5, -205892296168732025231884312642733794948394306764800000⟩,
  ⟨5, 2, 4, 1, 5, 5, -350058521932269053542642013544371450381432625561600000⟩,
  ⟨5, 2, 5, 1, 6, 5, -240910075029203085331669775871746459515949678592000000⟩,
  ⟨5, 2, 6, 1, 7, 5, -100278437772422358880285206821395210537355182080000000⟩,
  ⟨5, 2, 7, 1, 8, 5, -47128996750141246828664664201939237899436294144000000⟩,
  ⟨5, 2, 3, 2, 3, 5, 142823065901374899263187089054269876579855446835200000⟩,
  ⟨5, 2, 4, 2, 4, 5, 93332370814294238197618150478009488075435435622400000⟩,
  ⟨5, 2, 5, 2, 5, 5, 42140431685543246565403368064119342667753586688000000⟩,
  ⟨5, 2, 6, 2, 6, 5, 6922182256881620265620103731797238398083661824000000⟩,
  ⟨5, 2, 7, 2, 7, 5, 2782549950321217848645952621318111724914606080000000⟩,
  ⟨5, 2, 8, 2, 8, 5, 8996469999510968316674446657041518634934154035200000⟩,
  ⟨5, 2, 3, 3, 2, 5, -94179350991126437843137405173425238645343990579200000⟩,
  ⟨5, 2, 4, 3, 3, 5, -119043874983989394017543106741113261113252773888000000⟩,
  ⟨5, 2, 5, 3, 4, 5, -57035315180629307554275637025554516471336402944000000⟩,
  ⟨5, 2, 6, 3, 5, 5, -16863394262707143176017493149766003237830262784000000⟩,
  ⟨5, 2, 7, 3, 6, 5, 2172673696633001328682770613004859756137938944000000⟩,
  ⟨5, 2, 8, 3, 7, 5, 5510848525869265248069892136651500015589523456000000⟩,
  ⟨5, 2, 3, 4, 1, 5, 86959022698791585102235495264099589703776757350400000⟩,
  ⟨5, 2, 4, 4, 2, 5, 396881209174318841684579885359835411236790049177600000⟩,
  ⟨5, 2, 5, 4, 3, 5, 5320049286731971354124091784582756245285371904000000⟩,
  ⟨5, 2, 6, 4, 4, 5, 7793237294407813646111580081746284094863441920000000⟩,
  ⟨5, 2, 7, 4, 5, 5, 7480320047783731071836907343408346447090810880000000⟩,
  ⟨5, 2, 8, 4, 6, 5, -7029298273026028433226970796760621858280597094400000⟩,
  ⟨5, 2, 3, 5, 0, 5, -104449945088996816281664427676957179164671711641600000⟩,
  ⟨5, 2, 4, 5, 1, 5, -382643021721846954251949551717341176230768227123200000⟩,
  ⟨5, 2, 5, 5, 2, 5, 413212007262436537930532946668873185581223378944000000⟩,
  ⟨5, 2, 6, 5, 3, 5, 2886817928425124670473323355258605342411456512000000⟩,
  ⟨5, 2, 7, 5, 4, 5, -4739992459665041165575557866488999627267768320000000⟩,
  ⟨5, 2, 8, 5, 5, 5, -2349681986594217260493470874840875490417102028800000⟩,
  ⟨5, 2, 4, 6, 0, 5, -1193855261034377724703353708864981816684755445350400000⟩,
  ⟨5, 2, 5, 6, 1, 5, -527907075893857480842619114824491181216198819840000000⟩,
  ⟨5, 2, 6, 6, 2, 5, 206849085846936805655717253343306849303922737152000000⟩,
  ⟨5, 2, 7, 6, 3, 5, -14212954809700486208652968902812023964693430272000000⟩,
  ⟨5, 2, 8, 6, 4, 5, 3500211263189640115402849376197272463238548684800000⟩,
  ⟨5, 2, 5, 7, 0, 5, -2303221814218353536986704159585419885490022121472000000⟩,
  ⟨5, 2, 6, 7, 1, 5, -410068815871080178408830901906011472677197316096000000⟩,
  ⟨5, 2, 7, 7, 2, 5, 25239532241274929310703403533462242740171440128000000⟩,
  ⟨5, 2, 8, 7, 3, 5, 16764081692887536137180231484843275345556878131200000⟩
]

def collectedFourData_10_2_42 : List CollectedFourTerm := [
  ⟨5, 3, 2, 0, 4, 6, -656284757606650889695694936200884003391773081600000⟩,
  ⟨5, 3, 3, 0, 5, 6, 4511005128986296501238641888598442623505530880000000⟩,
  ⟨5, 3, 4, 0, 6, 6, 2367297916920814079475870009338314229079343104000000⟩,
  ⟨5, 3, 5, 0, 7, 6, 10200886080119112068537707589223474001870848000000⟩,
  ⟨5, 3, 6, 0, 8, 6, 157106300643542531790108085296735553629192192000000⟩,
  ⟨5, 3, 2, 1, 3, 6, 391831849623142093217844659579507710676592230400000⟩,
  ⟨5, 3, 3, 1, 4, 6, -4315268395821444646564240933186537302850220851200000⟩,
  ⟨5, 3, 4, 1, 5, 6, -3668414274092923652908498491053993113645429555200000⟩,
  ⟨5, 3, 5, 1, 6, 6, -1683067073340991058656210891341024014962262016000000⟩,
  ⟨5, 3, 6, 1, 7, 6, -525430505844489902942273301016807983682682880000000⟩,
  ⟨5, 3, 7, 1, 8, 6, -197554035762452844344718751023291549799887667200000⟩,
  ⟨5, 3, 2, 2, 2, 6, 95664012223400410974573839691958730433862041600000⟩,
  ⟨5, 3, 3, 2, 3, 6, 2993409049037184769340874906590283286801337548800000⟩,
  ⟨5, 3, 4, 2, 4, 6, 978070179352286673997959289835832841320844492800000⟩,
  ⟨5, 3, 5, 2, 5, 6, 294405175946733233756106589238897960156135424000000⟩,
  ⟨5, 3, 6, 2, 6, 6, 36270267123978978596602881877572043684184064000000⟩,
  ⟨5, 3, 7, 2, 7, 6, 11663816552490516980281994443146480272277504000000⟩,
  ⟨5, 3, 8, 2, 8, 6, 31425963465084394083646131221240496064875724800000⟩,
  ⟨5, 3, 2, 3, 1, 6, 548256614888674841342269835231143467637800960000000⟩,
  ⟨5, 3, 3, 3, 2, 6, -1973892100061500867081418064603238468026158284800000⟩,
  ⟨5, 3, 4, 3, 3, 6, -1247512124041634910053208660259818858438721536000000⟩,
  ⟨5, 3, 5, 3, 4, 6, -398465116025165641921153852283961756207808512000000⟩,
  ⟨5, 3, 6, 3, 5, 6, -88359391854686698045048916145285317340954624000000⟩,
  ⟨5, 3, 7, 3, 6, 6, 9107354002045252143036838364605440503001907200000⟩,
  ⟨5, 3, 8, 3, 7, 6, 19250186400332093712686980542581455762489344000000⟩,
  ⟨5, 3, 2, 4, 0, 6, -2099586023753100791432332574423535425076540211200000⟩,
  ⟨5, 3, 3, 4, 1, 6, 1822562229701349969021486940625465121017797017600000⟩,
  ⟨5, 3, 4, 4, 2, 6, 4159089414015264873917598716324206500241421107200000⟩,
  ⟨5, 3, 5, 4, 3, 6, 37167394439457973725341774325765887955566592000000⟩,
  ⟨5, 3, 6, 4, 4, 6, 40834347889023021834748987112355347426181120000000⟩,
  ⟨5, 3, 7, 4, 5, 6, 31355800380580587476091030212215690959519744000000⟩,
  ⟨5, 3, 8, 4, 6, 6, -24554349731095046246475684266384025563273625600000⟩,
  ⟨5, 3, 3, 5, 0, 6, -2189152073074425324552927910550266499249366630400000⟩,
  ⟨5, 3, 4, 5, 1, 6, -4009881305040947033226935220175988954948331110400000⟩,
  ⟨5, 3, 5, 5, 2, 6, 2886817928425124670473323355258605342411456512000000⟩,
  ⟨5, 3, 6, 5, 3, 6, 15126105253611140766152077425188409685573632000000⟩,
  ⟨5, 3, 7, 5, 4, 6, -19868970367751737356713574404713883910537216000000⟩,
  ⟨5, 3, 8, 5, 5, 6, -8207777080264887640216826943162968043631411200000⟩,
  ⟨5, 3, 4, 6, 0, 6, -12510924335179651441786292450048015861336034508800000⟩,
  ⟨5, 3, 5, 6, 1, 6, -3688110665828197310366822054976069566799544320000000⟩,
  ⟨5, 3, 6, 6, 2, 6, 1083830404864123330701966452611547700419100672000000⟩,
  ⟨5, 3, 7, 6, 3, 6, -59577474089924922577633256185512497904195993600000⟩,
  ⟨5, 3, 8, 6, 4, 6, 12226741297759431269564889414386939818357555200000⟩,
  ⟨5, 3, 5, 7, 0, 6, -16090970033701189724681656972138441782388064256000000⟩,
  ⟨5, 3, 6, 7, 1, 6, -2148644017003695096917573158363367774990893056000000⟩,
  ⟨5, 3, 7, 7, 2, 6, 105798378893042430220266153578294709737383526400000⟩,
  ⟨5, 3, 8, 7, 3, 6, 58559348148219382370296811987306597023796428800000⟩
]

def collectedFourData_10_2_43 : List CollectedFourTerm := [
  ⟨5, 4, 1, 0, 3, 7, 2303959319293077366780963179399335596729040896000000⟩,
  ⟨5, 4, 2, 0, 4, 7, 4310330446292721697270272530563150447644770304000000⟩,
  ⟨5, 4, 3, 0, 5, 7, -14813632745152157354524917179688703107897753600000000⟩,
  ⟨5, 4, 4, 0, 6, 7, -5182626478563272024673440796541203953662033920000000⟩,
  ⟨5, 4, 5, 0, 7, 7, -16749280453597812720030148336973329496801280000000⟩,
  ⟨5, 4, 6, 0, 8, 7, -206367758238917400407131699492576795343978496000000⟩,
  ⟨5, 4, 1, 1, 2, 7, 676138278678898527149512879584558819500359680000000⟩,
  ⟨5, 4, 2, 1, 3, 7, -2573463320124966519516823648802242618485374976000000⟩,
  ⟨5, 4, 3, 1, 4, 7, 14170855360305435758151073455829415287968497664000000⟩,
  ⟨5, 4, 4, 1, 5, 7, 8031106188773536283177664556598627517591453696000000⟩,
  ⟨5, 4, 5, 1, 6, 7, 2763501348039284395727092170177971503245557760000000⟩,
  ⟨5, 4, 6, 1, 7, 7, 690181839667196032112159138598430472342077440000000⟩,
  ⟨5, 4, 7, 1, 8, 7, 216248400628270258467202242676862193110089728000000⟩,
  ⟨5, 4, 1, 2, 1, 7, 2476851524617809118545792656379218147527360512000000⟩,
  ⟨5, 4, 2, 2, 2, 7, -628299681992893392801785039132456141092552704000000⟩,
  ⟨5, 4, 3, 2, 3, 7, -9830018153496700638583173840500987389947150336000000⟩,
  ⟨5, 4, 4, 2, 4, 7, -2141248202506590591779318876692968838313017344000000⟩,
  ⟨5, 4, 5, 2, 5, 7, -483396718696133649724286503716073151020400640000000⟩,
  ⟨5, 4, 6, 2, 6, 7, -47642988769017908072322779457692860082552832000000⟩,
  ⟨5, 4, 7, 2, 7, 7, -12767553266947759627380104897678374034472960000000⟩,
  ⟨5, 4, 8, 2, 8, 7, -29485521241815825138980703169383695715926016000000⟩,
  ⟨5, 4, 1, 3, 0, 7, 2173782167088795087431739448183405479142096896000000⟩,
  ⟨5, 4, 2, 3, 1, 7, -3600825940486675688014026164805932398569062400000000⟩,
  ⟨5, 4, 3, 3, 2, 7, 6482039326663118625860064039568299554563424256000000⟩,
  ⟨5, 4, 4, 3, 3, 7, 2731126200962712578374353521431412376632033280000000⟩,
  ⟨5, 4, 5, 3, 4, 7, 654257279893371921589125231454981345058488320000000⟩,
  ⟨5, 4, 6, 3, 5, 7, 116064916185493782600934512947310844666970112000000⟩,
  ⟨5, 4, 7, 3, 6, 7, -9969174911040092851826789701496644281827328000000⟩,
  ⟨5, 4, 8, 3, 7, 7, -18061555396592254524788064406095639588372480000000⟩,
  ⟨5, 4, 2, 4, 0, 7, 13789608028985786627551222770303483863239753728000000⟩,
  ⟨5, 4, 3, 4, 1, 7, -5985089077486496109876132344395178044997763072000000⟩,
  ⟨5, 4, 4, 4, 2, 7, -9105320783547467614610176747633383356976070656000000⟩,
  ⟨5, 4, 5, 4, 3, 7, -61026768489184465803604170753717832903557120000000⟩,
  ⟨5, 4, 6, 4, 4, 7, -53638159631328043634667748121471932233154560000000⟩,
  ⟨5, 4, 7, 4, 5, 7, -34322972226561771425277547976408305300930560000000⟩,
  ⟨5, 4, 8, 4, 6, 7, 23038205380069590551863933889953052284157952000000⟩,
  ⟨5, 4, 3, 5, 0, 7, 7188928832164834560376158362075760789697855488000000⟩,
  ⟨5, 4, 4, 5, 1, 7, 8778665701033609135937919559920892280561467392000000⟩,
  ⟨5, 4, 5, 5, 2, 7, -4739992459665041165575557866488999627267768320000000⟩,
  ⟨5, 4, 6, 5, 3, 7, -19868970367751737356713574404713883910537216000000⟩,
  ⟨5, 4, 7, 5, 4, 7, 21749153580052687558787709858085750010019840000000⟩,
  ⟨5, 4, 8, 5, 5, 7, 7700975841747020897581130527738079534383104000000⟩,
  ⟨5, 4, 4, 6, 0, 7, 27389644229967248486791855064106318765987201024000000⟩,
  ⟨5, 4, 5, 6, 1, 7, 6055670007554925694718033793699214529868595200000000⟩,
  ⟨5, 4, 6, 6, 2, 7, -1423670788802197399744099524557809047343988736000000⟩,
  ⟨5, 4, 7, 6, 3, 7, 65215238128114831303941416998856928226443264000000⟩,
  ⟨5, 4, 8, 6, 4, 7, -11471783216887423715236109887253385087811584000000⟩,
  ⟨5, 4, 5, 7, 0, 7, 26420466589678107495834076839351496655146844160000000⟩,
  ⟨5, 4, 6, 7, 1, 7, 2822361975466323797897366675133843512626249728000000⟩,
  ⟨5, 4, 7, 7, 2, 7, -115809986550689880217783665929442747048001536000000⟩,
  ⟨5, 4, 8, 7, 3, 7, -54943515276774153021973147363659267698589696000000⟩
]

def collectedFourData_10_2_44 : List CollectedFourTerm := [
  ⟨5, 5, 0, 0, 2, 8, 2705879587310989387891446164834364596249060966400000⟩,
  ⟨5, 5, 1, 0, 3, 8, 5710527766083595081418582309107653368121340723200000⟩,
  ⟨5, 5, 2, 0, 4, 8, 5341730969039518997612674867237833876049389158400000⟩,
  ⟨5, 5, 3, 0, 5, 8, -12238882344750249627914161704642378988561367040000000⟩,
  ⟨5, 5, 4, 0, 6, 8, -3211377492567489483752142382191709051385020416000000⟩,
  ⟨5, 5, 5, 0, 7, 8, -8302857632185878308021464172569479133475635200000⟩,
  ⟨5, 5, 6, 0, 8, 8, -85249538593513692201896567340735172304909107200000⟩,
  ⟨5, 5, 0, 1, 1, 8, -19936145269279077423212471366267363633883040972800000⟩,
  ⟨5, 5, 1, 1, 2, 8, 1675857026543558474870545192914215053301907456000000⟩,
  ⟨5, 5, 2, 1, 3, 8, -3189256342659820000385678157413066238601042329600000⟩,
  ⟨5, 5, 3, 1, 4, 8, 11707825788782925798778885031416733675856435609600000⟩,
  ⟨5, 5, 4, 1, 5, 8, 4976417606347846276202294119350585689123900620800000⟩,
  ⟨5, 5, 5, 1, 6, 8, 1369907102737375588942484741241419978252904038400000⟩,
  ⟨5, 5, 6, 1, 7, 8, 285110832619177693868646190066524438405316608000000⟩,
  ⟨5, 5, 7, 1, 8, 8, 76569587084165796386441116210062139134364876800000⟩,
  ⟨5, 5, 0, 2, 0, 8, -3205563242576462863173251561582486869337387827200000⟩,
  ⟨5, 5, 1, 2, 1, 8, 6139053448277168341468114068556639828013639270400000⟩,
  ⟨5, 5, 2, 2, 2, 8, -778642823550979877471867082045143890440644198400000⟩,
  ⟨5, 5, 3, 2, 3, 8, -8121467414316506182105756461726930078437631590400000⟩,
  ⟨5, 5, 4, 2, 4, 8, -1326809159790447156229401873487520825114571571200000⟩,
  ⟨5, 5, 5, 2, 5, 8, -239626660161253164800471990420226904579217817600000⟩,
  ⟨5, 5, 6, 2, 6, 8, -19681091874209227203821758134913234236761702400000⟩,
  ⟨5, 5, 7, 2, 7, 8, -4520756125293992346565756978910962517016576000000⟩,
  ⟨5, 5, 8, 2, 8, 8, -9135246352814305197775680220082954723288678400000⟩,
  ⟨5, 5, 1, 3, 0, 8, 5387874394582081243508580937756387588946735923200000⟩,
  ⟨5, 5, 2, 3, 1, 8, -4462452166970650610291191095720059627152343040000000⟩,
  ⟨5, 5, 3, 3, 2, 8, 5355399181138480101232137623015967659601061478400000⟩,
  ⟨5, 5, 4, 3, 3, 8, 1692322849700026401430217747426755984326918144000000⟩,
  ⟨5, 5, 5, 3, 4, 8, 324324681578126896596120163980733390382746828800000⟩,
  ⟨5, 5, 6, 3, 5, 8, 47945864393473145779859290346994523248682598400000⟩,
  ⟨5, 5, 7, 3, 6, 8, -3529901743968662495363792865032913422175436800000⟩,
  ⟨5, 5, 8, 3, 7, 8, -5595856919391255338378218998593783334961152000000⟩,
  ⟨5, 5, 2, 4, 0, 8, 17089264309817368262656773178812068713210891468800000⟩,
  ⟨5, 5, 3, 4, 1, 8, -4944823616352900526220548332708078457906318540800000⟩,
  ⟨5, 5, 4, 4, 2, 8, -5642047009916370044724016182614306810881690828800000⟩,
  ⟨5, 5, 5, 4, 3, 8, -30251841081879158885023605542694555600342220800000⟩,
  ⟨5, 5, 6, 4, 4, 8, -22157668419705832507441289310430664476065792000000⟩,
  ⟨5, 5, 7, 4, 5, 8, -12153134096038041715526154141877160311259136000000⟩,
  ⟨5, 5, 8, 4, 6, 8, 7137729733439393045582588236880593241820364800000⟩,
  ⟨5, 5, 3, 5, 0, 8, 5939424560828377485979443240715821564248142643200000⟩,
  ⟨5, 5, 4, 5, 1, 8, 5439637520412008040872884650771011445741689241600000⟩,
  ⟨5, 5, 5, 5, 2, 8, -2349681986594217260493470874840875490417102028800000⟩,
  ⟨5, 5, 6, 5, 3, 8, -8207777080264887640216826943162968043631411200000⟩,
  ⟨5, 5, 7, 5, 4, 8, 7700975841747020897581130527738079534383104000000⟩,
  ⟨5, 5, 8, 5, 5, 8, 2385927347001111375330368015197313632410009600000⟩,
  ⟨5, 5, 4, 6, 0, 8, 16971797480171035784005007710492955217017123635200000⟩,
  ⟨5, 5, 5, 6, 1, 8, 3001882145296953362085617056193377840417210368000000⟩,
  ⟨5, 5, 6, 6, 2, 8, -588111626012532961756743298945409033788666675200000⟩,
  ⟨5, 5, 7, 6, 3, 8, 23091518090111113590794032793603010669733478400000⟩,
  ⟨5, 5, 8, 6, 4, 8, -3554204279886536661071602674948180375345561600000⟩,
  ⟨5, 5, 5, 7, 0, 8, 13097002780373190041989683270142368121025357414400000⟩,
  ⟨5, 5, 6, 7, 1, 8, 1165904297287694966802578737163753078778337689600000⟩,
  ⟨5, 5, 7, 7, 2, 8, -41006189292712220276356662940360180950997401600000⟩,
  ⟨5, 5, 8, 7, 3, 8, -17022678467394050867453311090856154922116710400000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1009
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1009. -/
namespace LaughlinFock
def collectedFourData_10_2_45 : List CollectedFourTerm := [
  ⟨6, 0, 4, 0, 6, 4, -326335217833134928190318362464016013112194472345600000⟩,
  ⟨6, 0, 5, 0, 7, 4, -4218617805455555629578227747977761955608369561600000⟩,
  ⟨6, 0, 6, 0, 8, 4, -129943895469198926588407086724608849819103710412800000⟩,
  ⟨6, 0, 4, 1, 5, 4, 505695866448202418599527182874998328177512970977280000⟩,
  ⟨6, 0, 5, 1, 6, 4, 696039213417955327868690350268388120480424604467200000⟩,
  ⟨6, 0, 6, 1, 7, 4, 434587832875632341679286990215004212774611976192000000⟩,
  ⟨6, 0, 7, 1, 8, 4, 272330908727409885097427855092506939428417883340800000⟩,
  ⟨6, 0, 4, 2, 4, 4, -134828296326211113969557327566346022229246916689920000⟩,
  ⟨6, 0, 5, 2, 5, 4, -121752454395869726259662954988323269623856024780800000⟩,
  ⟨6, 0, 6, 2, 6, 4, -29999432107384212396055704701145000924379978137600000⟩,
  ⟨6, 0, 7, 2, 7, 4, -16078728782787327603765330377467919125557805056000000⟩,
  ⟨6, 0, 8, 2, 8, 4, -64981673153756450429386670955626653478143446220800000⟩,
  ⟨6, 0, 4, 3, 3, 4, 171971232618721334195957518219582616044537538150400000⟩,
  ⟨6, 0, 5, 3, 4, 4, 164786864603143330816210467745522746658988123750400000⟩,
  ⟨6, 0, 6, 3, 5, 4, 73082769639763171538503191303678851362714130841600000⟩,
  ⟨6, 0, 7, 3, 6, 4, -12554610600117067412325393375583261009736682700800000⟩,
  ⟨6, 0, 8, 3, 7, 4, -39804963249737178190417870975494147261515956224000000⟩,
  ⟨6, 0, 4, 4, 2, 4, -573336097754677790685317843829627782169849055150080000⟩,
  ⟨6, 0, 5, 4, 3, 4, -15370726693073351058269916762997952827156227686400000⟩,
  ⟨6, 0, 6, 4, 4, 4, -33774420325020928082688378411244854661934481408000000⟩,
  ⟨6, 0, 7, 4, 5, 4, -43224394675422415144083347217627224976094396416000000⟩,
  ⟨6, 0, 8, 4, 6, 4, 50772754525149479431273175024892363206261578137600000⟩,
  ⟨6, 0, 4, 5, 1, 4, 552767558241096625370707186652223351751602402754560000⟩,
  ⟨6, 0, 5, 5, 2, 4, -1193855261034377724703353708864981816684755445350400000⟩,
  ⟨6, 0, 6, 5, 3, 4, -12510924335179651441786292450048015861336034508800000⟩,
  ⟨6, 0, 7, 5, 4, 4, 27389644229967248486791855064106318765987201024000000⟩,
  ⟨6, 0, 8, 5, 5, 4, 16971797480171035784005007710492955217017123635200000⟩,
  ⟨6, 0, 4, 6, 0, 4, 1724647831197026377866482490707069904957806550712320000⟩,
  ⟨6, 0, 5, 6, 1, 4, 1525233122020288667778756863876494698355196166144000000⟩,
  ⟨6, 0, 6, 6, 2, 4, -896444918243907224731608026397337659173749181644800000⟩,
  ⟨6, 0, 7, 6, 3, 4, 82128353369112277417750627982654326891065271910400000⟩,
  ⟨6, 0, 8, 6, 4, 4, -25282092230180274559811345672306178832486052659200000⟩,
  ⟨6, 0, 5, 7, 0, 4, 6654485910152521909610319994051665535774527533875200000⟩,
  ⟨6, 0, 6, 7, 1, 4, 1777160892990091525364647665461730092091693229670400000⟩,
  ⟨6, 0, 7, 7, 2, 4, -145844495429463215804624236647021900628806441369600000⟩,
  ⟨6, 0, 8, 7, 3, 4, -121087279493991033257359627927270695396803661004800000⟩
]

def collectedFourData_10_2_46 : List CollectedFourTerm := [
  ⟨6, 1, 3, 0, 5, 5, -274973065618596652508273941146704637347443507200000000⟩,
  ⟨6, 1, 4, 0, 6, 5, -288602272369622751127947246288081713437889003520000000⟩,
  ⟨6, 1, 5, 0, 7, 5, -1865417243345109067357990031284186176144015360000000⟩,
  ⟨6, 1, 6, 0, 8, 5, -38306319661099216401486708513809988117772369920000000⟩,
  ⟨6, 1, 3, 1, 4, 5, 263041727029184897099245994961599285562156515328000000⟩,
  ⟨6, 1, 4, 1, 5, 5, 447224106407977604014293236118454210661424562176000000⟩,
  ⟨6, 1, 5, 1, 6, 5, 307779374816820992232872525313284123906927493120000000⟩,
  ⟨6, 1, 6, 1, 7, 5, 128112678066545600680933938961819560930233548800000000⟩,
  ⟨6, 1, 7, 1, 8, 5, 60210570910096337020110081408335766894768291840000000⟩,
  ⟨6, 1, 3, 2, 3, 5, -182466399245520175154606214112712461090314780672000000⟩,
  ⟨6, 1, 4, 2, 4, 5, -119238594466890003546771792725151544419563864064000000⟩,
  ⟨6, 1, 5, 2, 5, 5, -53837332112885848782424160676634624683336007680000000⟩,
  ⟨6, 1, 6, 2, 6, 5, -8843569232763953728378375425579739479948656640000000⟩,
  ⟨6, 1, 7, 2, 7, 5, -3554901072537653978837638252050343242026188800000000⟩,
  ⟨6, 1, 8, 2, 8, 5, -11493616079245015531633827699164610203769372672000000⟩,
  ⟨6, 1, 3, 3, 2, 5, 120320670545593042173615712816448229488052928512000000⟩,
  ⟨6, 1, 4, 3, 3, 5, 152086829136982532374026404130015757356163399680000000⟩,
  ⟨6, 1, 5, 3, 4, 5, 72866581634854826814341107886804019007287459840000000⟩,
  ⟨6, 1, 6, 3, 5, 5, 21544158926671765780600764209506728850741002240000000⟩,
  ⟨6, 1, 7, 3, 6, 5, -2775741744921196501763452347712404761440419840000000⟩,
  ⟨6, 1, 8, 3, 7, 5, -7040492240918682745617820139997388731486044160000000⟩,
  ⟨6, 1, 3, 4, 1, 5, -111096199018125198971903169833411169958068486144000000⟩,
  ⟨6, 1, 4, 4, 2, 5, -507043345619350220024867097272538377499690663936000000⟩,
  ⟨6, 1, 5, 4, 3, 5, -6796732943886033052530347408079169663732285440000000⟩,
  ⟨6, 1, 6, 4, 4, 5, -9956402620277349251237736389722645778871091200000000⟩,
  ⟨6, 1, 7, 4, 5, 5, -9556629076046430295343885538556309255539916800000000⟩,
  ⟨6, 1, 8, 4, 6, 5, 8980417392716575309377252673497022522913193984000000⟩,
  ⟨6, 1, 3, 5, 0, 5, 133442068768796000201890350531238776308263550976000000⟩,
  ⟨6, 1, 4, 5, 1, 5, 488853070961408701696516664144925706017520484352000000⟩,
  ⟨6, 1, 5, 5, 2, 5, -527907075893857480842619114824491181216198819840000000⟩,
  ⟨6, 1, 6, 5, 3, 5, -3688110665828197310366822054976069566799544320000000⟩,
  ⟨6, 1, 7, 5, 4, 5, 6055670007554925694718033793699214529868595200000000⟩,
  ⟨6, 1, 8, 5, 5, 5, 3001882145296953362085617056193377840417210368000000⟩,
  ⟨6, 1, 4, 6, 0, 5, 1525233122020288667778756863876494698355196166144000000⟩,
  ⟨6, 1, 5, 6, 1, 5, 674438002479937200218757118435996292153239142400000000⟩,
  ⟨6, 1, 6, 6, 2, 5, -264264092382536589913437143090086122200204574720000000⟩,
  ⟨6, 1, 7, 6, 3, 5, 18158038202009915458896262457938000933206097920000000⟩,
  ⟨6, 1, 8, 6, 4, 5, -4471763309113217575180910952109522214115606528000000⟩,
  ⟨6, 1, 5, 7, 0, 5, 2942526044038042989243942194243380364303054929920000000⟩,
  ⟨6, 1, 6, 7, 1, 5, 523891430299774274423675598949482216074835394560000000⟩,
  ⟨6, 1, 7, 7, 2, 5, -32245257708491159871796809633894037045987246080000000⟩,
  ⟨6, 1, 8, 7, 3, 5, -21417280212085730766366737760495431668551647232000000⟩
]

def collectedFourData_10_2_47 : List CollectedFourTerm := [
  ⟨6, 2, 2, 0, 4, 6, -47024753736468710097188565875612986307314817433600000⟩,
  ⟨6, 2, 3, 0, 5, 6, 323226926781177639383210877090443432483597844480000000⟩,
  ⟨6, 2, 4, 0, 6, 6, 169623932711809328589063576900049124436668841984000000⟩,
  ⟨6, 2, 5, 0, 7, 6, 730923810512876636762400409455850344476049408000000⟩,
  ⟨6, 2, 6, 0, 8, 6, 11257133450961825648597525858412083426657042432000000⟩,
  ⟨6, 2, 2, 1, 3, 6, 28075916774036878925151360066678973067939964518400000⟩,
  ⟨6, 2, 3, 1, 4, 6, -309201808008306772052428530988323766235378692915200000⟩,
  ⟨6, 2, 4, 1, 5, 6, -262852787365753925402813763855125028768956232499200000⟩,
  ⟨6, 2, 5, 1, 6, 6, -120596758843599189021115974011112599530594369536000000⟩,
  ⟨6, 2, 6, 1, 7, 6, -37648657623973627256479069565832094412156436480000000⟩,
  ⟨6, 2, 7, 1, 8, 6, -14155333906052508947543575353885254970728723251200000⟩,
  ⟨6, 2, 2, 2, 2, 6, 6854610844008344176782067722963286032356317593600000⟩,
  ⟨6, 2, 3, 2, 3, 6, 214486656488613344016173413308414045099209313484800000⟩,
  ⟨6, 2, 4, 2, 4, 6, 70081635735004550063136512400578333503545724108800000⟩,
  ⟨6, 2, 5, 2, 5, 6, 21095005997281706625576368607417111190337224704000000⟩,
  ⟨6, 2, 6, 2, 6, 6, 2598872455427820338792172112432595624886534144000000⟩,
  ⟨6, 2, 7, 2, 7, 6, 835747127525022325925083738886242567804944384000000⟩,
  ⟨6, 2, 8, 2, 8, 6, 2251763698224705349537339487520806266754354380800000⟩,
  ⟨6, 2, 2, 3, 1, 6, 39284216189251054292794859168648790624341852160000000⟩,
  ⟨6, 2, 3, 3, 2, 6, -141435236506569235808233868424446222441152040140800000⟩,
  ⟨6, 2, 4, 3, 3, 6, -89387952007682554741156992344180521926138003456000000⟩,
  ⟨6, 2, 5, 3, 4, 6, -28551210029606445890468285611886292239124529152000000⟩,
  ⟨6, 2, 6, 3, 5, 6, -6331213081077159870191331749434335891139067904000000⟩,
  ⟨6, 2, 7, 3, 6, 6, 652568986515618821352946288198366845469930291200000⟩,
  ⟨6, 2, 8, 3, 7, 6, 1379333078156441370989620877334879655925121024000000⟩,
  ⟨6, 2, 2, 4, 0, 6, -150441579773359858997923650164743415877216711475200000⟩,
  ⟨6, 2, 3, 4, 1, 6, 130592001456269609152623872697350039696016251289600000⟩,
  ⟨6, 2, 4, 4, 2, 6, 298011119708564363218684935438960419465017373491200000⟩,
  ⟨6, 2, 5, 4, 3, 6, 2663154294357781018440842827712631040043384832000000⟩,
  ⟨6, 2, 6, 4, 4, 6, 2925902409303705999093389108506954063958507520000000⟩,
  ⟨6, 2, 7, 4, 5, 6, 2246736304655159627421490127851754386750439424000000⟩,
  ⟨6, 2, 8, 4, 6, 6, -1759392147815090014658484339907055436156213657600000⟩,
  ⟨6, 2, 3, 5, 0, 6, -156859253448798292455295568034532256615380706918400000⟩,
  ⟨6, 2, 4, 5, 1, 6, -287319915168648994426613334145665641328901776998400000⟩,
  ⟨6, 2, 5, 5, 2, 6, 206849085846936805655717253343306849303922737152000000⟩,
  ⟨6, 2, 6, 5, 3, 6, 1083830404864123330701966452611547700419100672000000⟩,
  ⟨6, 2, 7, 5, 4, 6, -1423670788802197399744099524557809047343988736000000⟩,
  ⟨6, 2, 8, 5, 5, 6, -588111626012532961756743298945409033788666675200000⟩,
  ⟨6, 2, 4, 6, 0, 6, -896444918243907224731608026397337659173749181644800000⟩,
  ⟨6, 2, 5, 6, 1, 6, -264264092382536589913437143090086122200204574720000000⟩,
  ⟨6, 2, 6, 6, 2, 6, 77659670272854242686137091164578385332652736512000000⟩,
  ⟨6, 2, 7, 6, 3, 6, -4268903116897823809615340756380969847976728985600000⟩,
  ⟨6, 2, 8, 6, 4, 6, 876082358858096956648821614065982856085320499200000⟩,
  ⟨6, 2, 5, 7, 0, 6, -1152965834487983267697391521220889357567001624576000000⟩,
  ⟨6, 2, 6, 7, 1, 6, -153956730818201316162993740118159115619061989376000000⟩,
  ⟨6, 2, 7, 7, 2, 6, 7580768341026773953702357593021833336538424934400000⟩,
  ⟨6, 2, 8, 7, 3, 6, 4195951366721555306343310143872107626160245964800000⟩
]

def collectedFourData_10_2_48 : List CollectedFourTerm := [
  ⟨6, 3, 1, 0, 3, 7, 6908464510682967075694846332303980127009216921600000⟩,
  ⟨6, 3, 2, 0, 4, 7, 12924605338373005099847469898281017759045674598400000⟩,
  ⟨6, 3, 3, 0, 5, 7, -44418950993273413729821001652391233186231746560000000⟩,
  ⟨6, 3, 4, 0, 6, 7, -15540201078839327636141492937573897346882732032000000⟩,
  ⟨6, 3, 5, 0, 7, 7, -50223026346081575830142019268876676930469888000000⟩,
  ⟨6, 3, 6, 0, 8, 7, -618797529107504087616605017977777695135209881600000⟩,
  ⟨6, 3, 1, 1, 2, 7, 2027413098596143854632254671623864221358358528000000⟩,
  ⟨6, 3, 2, 1, 3, 7, -7716577227623408635688711726181047231441377689600000⟩,
  ⟨6, 3, 3, 1, 4, 7, 42491571150106003914965420826434401806030628454400000⟩,
  ⟨6, 3, 4, 1, 5, 7, 24081420024244185788429628842771967447748155801600000⟩,
  ⟨6, 3, 5, 1, 6, 7, 8286409759184370223568490569857965385838493696000000⟩,
  ⟨6, 3, 6, 1, 7, 7, 2069522975224101657727005074677878559787188224000000⟩,
  ⟨6, 3, 7, 1, 8, 7, 648424817540069891759187268385657418089811148800000⟩,
  ⟨6, 3, 1, 2, 1, 7, 7426884976989683453558108340953996524115931955200000⟩,
  ⟨6, 3, 2, 2, 2, 7, -1883968184148805987813478799731909548424193638400000⟩,
  ⟨6, 3, 3, 2, 3, 7, -29475490727691389549668780073991238790755752345600000⟩,
  ⟨6, 3, 4, 2, 4, 7, -6420572226127379711060642729552324108120122982400000⟩,
  ⟨6, 3, 5, 2, 5, 7, -1449473976266865161833858788684685576916434944000000⟩,
  ⟨6, 3, 6, 2, 6, 7, -142858380500666661384438585675716655198712627200000⟩,
  ⟨6, 3, 7, 2, 7, 7, -38283743942157197899373018308736614574063616000000⟩,
  ⟨6, 3, 8, 2, 8, 7, -88412879243273471318064261372537076033624473600000⟩,
  ⟨6, 3, 1, 3, 0, 7, 6518125918949065154638010946771297198986074521600000⟩,
  ⟨6, 3, 2, 3, 1, 7, -10797142992364796370011452472137229574120407040000000⟩,
  ⟨6, 3, 3, 3, 2, 7, 19436514468859451557100562812214841872699988377600000⟩,
  ⟨6, 3, 4, 3, 3, 7, 8189332283582386037124397721806737671442137088000000⟩,
  ⟨6, 3, 5, 3, 4, 7, 1961802520187802312914413402117477718946742272000000⟩,
  ⟨6, 3, 6, 3, 5, 7, 348022791760447436499756304663062090377016115200000⟩,
  ⟨6, 3, 7, 3, 6, 7, -29892754831644931929523420727688803017084108800000⟩,
  ⟨6, 3, 8, 3, 7, 7, -54157906964857983342485995192003942215057408000000⟩,
  ⟨6, 3, 2, 4, 0, 7, 41348393995822513934104474768657570085825465548800000⟩,
  ⟨6, 3, 3, 4, 1, 7, -17946399981479895875968105293568578606010151731200000⟩,
  ⟨6, 3, 4, 4, 2, 7, -27302472298348758100143103538981071231016081817600000⟩,
  ⟨6, 3, 5, 4, 3, 7, -182989890827827710924229683321122167562698752000000⟩,
  ⟨6, 3, 6, 4, 4, 7, -160835010899877989193858358265311510948478976000000⟩,
  ⟨6, 3, 7, 4, 5, 7, -102918065237850747672377499440842391553048576000000⟩,
  ⟨6, 3, 8, 4, 6, 7, 69080483724370064343819754320767552626832179200000⟩,
  ⟨6, 3, 3, 5, 0, 7, 21556135688226833768493053930650716589244861644800000⟩,
  ⟨6, 3, 4, 5, 1, 7, 26322991008950981301798815417105948407405687603200000⟩,
  ⟨6, 3, 5, 5, 2, 7, -14212954809700486208652968902812023964693430272000000⟩,
  ⟨6, 3, 6, 5, 3, 7, -59577474089924922577633256185512497904195993600000⟩,
  ⟨6, 3, 7, 5, 4, 7, 65215238128114831303941416998856928226443264000000⟩,
  ⟨6, 3, 8, 5, 5, 7, 23091518090111113590794032793603010669733478400000⟩,
  ⟨6, 3, 4, 6, 0, 7, 82128353369112277417750627982654326891065271910400000⟩,
  ⟨6, 3, 5, 6, 1, 7, 18158038202009915458896262457938000933206097920000000⟩,
  ⟨6, 3, 6, 6, 2, 7, -4268903116897823809615340756380969847976728985600000⟩,
  ⟨6, 3, 7, 6, 3, 7, 195549094287853175463438656407923179896858214400000⟩,
  ⟨6, 3, 8, 6, 4, 7, -34398353549242451167980564443836414800848486400000⟩,
  ⟨6, 3, 5, 7, 0, 7, 79222256340220561197132071472782259980794331136000000⟩,
  ⟨6, 3, 6, 7, 1, 7, 8462904436087347085415931037486217928312147148800000⟩,
  ⟨6, 3, 7, 7, 2, 7, -347258380548836066314076772302157659867027865600000⟩,
  ⟨6, 3, 8, 7, 3, 7, -164749143877343534869764083734364472141781401600000⟩
]

def collectedFourData_10_2_49 : List CollectedFourTerm := [
  ⟨6, 4, 0, 0, 2, 8, -4030822154818050410845093447836384849092306534400000⟩,
  ⟨6, 4, 1, 0, 3, 8, -8506705894517651792398791776545472237343552307200000⟩,
  ⟨6, 4, 2, 0, 4, 8, -7957326569908279651654604038420259299798705766400000⟩,
  ⟨6, 4, 3, 0, 5, 8, 18231690108005139543084667861435814451703971840000000⟩,
  ⟨6, 4, 4, 0, 6, 8, 4783838721141641308661988775168032336129294336000000⟩,
  ⟨6, 4, 5, 0, 7, 8, 12368378345088769619507077074591009492644659200000⟩,
  ⟨6, 4, 6, 0, 8, 8, 126992246980300742460627894041115686056702771200000⟩,
  ⟨6, 4, 0, 1, 1, 8, 29697942365920005662230663698561285503266376908800000⟩,
  ⟨6, 4, 1, 1, 2, 8, -2496445762988384204048577509245842701131186176000000⟩,
  ⟨6, 4, 2, 1, 3, 8, 4750885879649350085050846642434546211552336281600000⟩,
  ⟨6, 4, 3, 1, 4, 8, -17440600016157515799977228149422082115440843161600000⟩,
  ⟨6, 4, 4, 1, 5, 8, -7413136354388745211560310158780297358613466316800000⟩,
  ⟨6, 4, 5, 1, 6, 8, -2040686483482381507601636331295581041712326246400000⟩,
  ⟨6, 4, 6, 1, 7, 8, -424716260874737911045076930525083128003821568000000⟩,
  ⟨6, 4, 7, 1, 8, 8, -114062129538750027537389554683843570075225292800000⟩,
  ⟨6, 4, 0, 2, 0, 8, 4775177505104023443017797241703688213208707891200000⟩,
  ⟨6, 4, 1, 2, 1, 8, -9145060543332943846232913682272059519966537318400000⟩,
  ⟨6, 4, 2, 2, 2, 8, 1159907764771741379950907129543836503351125606400000⟩,
  ⟨6, 4, 3, 2, 3, 8, 12098169828684781460686282885051616066282088038400000⟩,
  ⟨6, 4, 4, 2, 4, 8, 1976485495355559278550569727833029297124356915200000⟩,
  ⟨6, 4, 5, 2, 5, 8, 356960618348470579106062502936855325976402329600000⟩,
  ⟨6, 4, 6, 2, 6, 8, 29318001262727465289483646384357718790399590400000⟩,
  ⟨6, 4, 7, 2, 7, 8, 6734358776279913007671558168404585607069696000000⟩,
  ⟨6, 4, 8, 2, 8, 8, 13608348856808402239596902293530798253827686400000⟩,
  ⟨6, 4, 1, 3, 0, 8, -8026064270894077554918607724359742355949171507200000⟩,
  ⟨6, 4, 2, 3, 1, 8, 6647506098863893208279683279993625210876067840000000⟩,
  ⟨6, 4, 3, 3, 2, 8, -7977687465642001198398192169853958022083536486400000⟩,
  ⟨6, 4, 4, 3, 3, 8, -2520974128953982856775176267013299425115111424000000⟩,
  ⟨6, 4, 5, 3, 4, 8, -483131296008100899139655167142500674908769484800000⟩,
  ⟨6, 4, 6, 3, 5, 8, -71422709767055779295816531953618840061372006400000⟩,
  ⟨6, 4, 7, 3, 6, 8, 5258329387842221673222231026630913208143052800000⟩,
  ⟨6, 4, 8, 3, 7, 8, 8335886102119364244759777178007886618427392000000⟩,
  ⟨6, 4, 2, 4, 0, 8, -25457077067500848315484351409513753509379230924800000⟩,
  ⟨6, 4, 3, 4, 1, 8, 7366072266456701278500952032234369013856914636800000⟩,
  ⟨6, 4, 4, 4, 2, 8, 8404693317745210702793938429100889044496993484800000⟩,
  ⟨6, 4, 5, 4, 3, 8, 45064751524310424948139200270404098045299916800000⟩,
  ⟨6, 4, 6, 4, 4, 8, 33007241410183870013421684277669018397048832000000⟩,
  ⟨6, 4, 7, 4, 5, 8, 18103954955906410274378101328033375066259456000000⟩,
  ⟨6, 4, 8, 4, 6, 8, -10632741855761068263699595785575338062171340800000⟩,
  ⟨6, 4, 3, 5, 0, 8, -8847682734636764095825027320511841966633464627200000⟩,
  ⟨6, 4, 4, 5, 1, 8, -8103173376331119792328922816741958806419380633600000⟩,
  ⟨6, 4, 5, 5, 2, 8, 3500211263189640115402849376197272463238548684800000⟩,
  ⟨6, 4, 6, 5, 3, 8, 12226741297759431269564889414386939818357555200000⟩,
  ⟨6, 4, 7, 5, 4, 8, -11471783216887423715236109887253385087811584000000⟩,
  ⟨6, 4, 8, 5, 5, 8, -3554204279886536661071602674948180375345561600000⟩,
  ⟨6, 4, 4, 6, 0, 8, -25282092230180274559811345672306178832486052659200000⟩,
  ⟨6, 4, 5, 6, 1, 8, -4471763309113217575180910952109522214115606528000000⟩,
  ⟨6, 4, 6, 6, 2, 8, 876082358858096956648821614065982856085320499200000⟩,
  ⟨6, 4, 7, 6, 3, 8, -34398353549242451167980564443836414800848486400000⟩,
  ⟨6, 4, 8, 6, 4, 8, 5294531737959869411886435813279901400275353600000⟩,
  ⟨6, 4, 5, 7, 0, 8, -19509991951010811502018227490148766683142448742400000⟩,
  ⟨6, 4, 6, 7, 1, 8, -1736793053890127618772335819969288216900114841600000⟩,
  ⟨6, 4, 7, 7, 2, 8, 61085000626352835293562259042122043619907993600000⟩,
  ⟨6, 4, 8, 7, 3, 8, 25357887255028869901670026023577577616467558400000⟩
]

def collectedFourData_10_2_50 : List CollectedFourTerm := [
  ⟨7, 0, 3, 0, 5, 5, -1199688339056445036341049542717885286042052853760000000⟩,
  ⟨7, 0, 4, 0, 6, 5, -1259151619116299632924388922916719925922277359616000000⟩,
  ⟨7, 0, 5, 0, 7, 5, -8138685544641918331715189348369213491865714688000000⟩,
  ⟨7, 0, 6, 0, 8, 5, -167127805431432574908111227536980467271635828736000000⟩,
  ⟨7, 0, 3, 1, 4, 5, 1147632739564000068745151178184047317822946567782400000⟩,
  ⟨7, 0, 4, 1, 5, 5, 1951207636266406591150729601785807371094952037580800000⟩,
  ⟨7, 0, 5, 1, 6, 5, 1342819981801341443261784786564243562275375415296000000⟩,
  ⟨7, 0, 6, 1, 7, 5, 558946693982425493528928941171227417549775831040000000⟩,
  ⟨7, 0, 7, 1, 8, 5, 262694528448711239488724074081088769450754179072000000⟩,
  ⟨7, 0, 3, 2, 3, 5, -796088194863779774992011632769192546054279109017600000⟩,
  ⟨7, 0, 4, 2, 4, 5, -520229685135145669226313366806078299091995145011200000⟩,
  ⟨7, 0, 5, 2, 5, 5, -234888531341922436618694281641583262283904057344000000⟩,
  ⟨7, 0, 6, 2, 6, 5, -38583876789231740176400972665172589682372902912000000⟩,
  ⟨7, 0, 7, 2, 7, 5, -15509785853492128499808801564768180607427543040000000⟩,
  ⟨7, 0, 8, 2, 8, 5, -50145846658987671225234583352443023525620062617600000⟩,
  ⟨7, 0, 3, 3, 2, 5, 524950707722109053219454279592353667371048212889600000⟩,
  ⟨7, 0, 4, 3, 3, 5, 663544245794553277768509612446019425723895250944000000⟩,
  ⟨7, 0, 5, 3, 4, 5, 317911822009114455075127336186368654899750633472000000⟩,
  ⟨7, 0, 6, 3, 5, 5, 93995665288022048354520476052984548239073083392000000⟩,
  ⟨7, 0, 7, 3, 6, 5, -12110367959577115963415515632814972185159401472000000⟩,
  ⟨7, 0, 8, 3, 7, 5, -30717177421162978455077341139072206149651529728000000⟩,
  ⟨7, 0, 3, 4, 1, 5, -484704980743121153694800770053088705280774189875200000⟩,
  ⟨7, 0, 4, 4, 2, 5, -2212194811761817349415141820919763225037691997388800000⟩,
  ⟨7, 0, 5, 4, 3, 5, -29653672581047872608521443100361814189855997952000000⟩,
  ⟨7, 0, 6, 4, 4, 5, -43439091372918630553794289021691732687805480960000000⟩,
  ⟨7, 0, 7, 4, 5, 5, -41694907235471739317048848181171275062250045440000000⟩,
  ⟨7, 0, 8, 4, 6, 5, 39180935782435865853291529448767317270338941747200000⟩,
  ⟨7, 0, 3, 5, 0, 5, 582198454533525950489730126791099409316981820620800000⟩,
  ⟨7, 0, 4, 5, 1, 5, 2132831910008975562387939671228271000407183563161600000⟩,
  ⟨7, 0, 5, 5, 2, 5, -2303221814218353536986704159585419885490022121472000000⟩,
  ⟨7, 0, 6, 5, 3, 5, -16090970033701189724681656972138441782388064256000000⟩,
  ⟨7, 0, 7, 5, 4, 5, 26420466589678107495834076839351496655146844160000000⟩,
  ⟨7, 0, 8, 5, 5, 5, 13097002780373190041989683270142368121025357414400000⟩,
  ⟨7, 0, 4, 6, 0, 5, 6654485910152521909610319994051665535774527533875200000⟩,
  ⟨7, 0, 5, 6, 1, 5, 2942526044038042989243942194243380364303054929920000000⟩,
  ⟨7, 0, 6, 6, 2, 5, -1152965834487983267697391521220889357567001624576000000⟩,
  ⟨7, 0, 7, 6, 3, 5, 79222256340220561197132071472782259980794331136000000⟩,
  ⟨7, 0, 8, 6, 4, 5, -19509991951010811502018227490148766683142448742400000⟩,
  ⟨7, 0, 5, 7, 0, 5, 12838036243516307282852552448451073626986812276736000000⟩,
  ⟨7, 0, 6, 7, 1, 5, 2285701832098769529342727082631522179386649346048000000⟩,
  ⟨7, 0, 7, 7, 2, 5, -140683814160926103885544808376069273268009304064000000⟩,
  ⟨7, 0, 8, 7, 3, 5, -93442102290784828500151889628044154440406112665600000⟩
]

def collectedFourData_10_2_51 : List CollectedFourTerm := [
  ⟨7, 1, 2, 0, 4, 6, 93224415289957355207680338836067562387766299852800000⟩,
  ⟨7, 1, 3, 0, 5, 6, -640782542403334916131861509151348409750299607040000000⟩,
  ⟨7, 1, 4, 0, 6, 6, -336271658855665660139162627262224982866323832832000000⟩,
  ⟨7, 1, 5, 0, 7, 6, -1449022896290608608864759275565619609583222784000000⟩,
  ⟨7, 1, 6, 0, 8, 6, -22316750230912382888265690207052941062660161536000000⟩,
  ⟨7, 1, 2, 1, 3, 6, -55659215987754848930968708224401822440439886643200000⟩,
  ⟨7, 1, 3, 1, 4, 6, 612978388355014846146587708607452993207286733209600000⟩,
  ⟨7, 1, 4, 1, 5, 6, 521093582899601427469058123768157734577500690841600000⟩,
  ⟨7, 1, 5, 1, 6, 6, 239077537589307537888970503651028721467945648128000000⟩,
  ⟨7, 1, 6, 1, 7, 6, 74636735220685081627899993449260129719460823040000000⟩,
  ⟨7, 1, 7, 1, 8, 6, 28062299571437360227288037939266719558997219737600000⟩,
  ⟨7, 1, 2, 2, 2, 6, -13588951290505269508034801450282126952652131532800000⟩,
  ⟨7, 1, 3, 2, 3, 6, -425209949013343975023735608469502850347890533990400000⟩,
  ⟨7, 1, 4, 2, 4, 6, -138933625268362646323881611808159584193308157542400000⟩,
  ⟨7, 1, 5, 2, 5, 6, -41819880879240282450410084950829616044433211392000000⟩,
  ⟨7, 1, 6, 2, 6, 6, -5152145323890175214493605221987816822655680512000000⟩,
  ⟨7, 1, 7, 2, 7, 6, -1656830309636670498361414671001264779304108032000000⟩,
  ⟨7, 1, 8, 2, 8, 6, -4464018149133934910934707471524698794353911398400000⟩,
  ⟨7, 1, 2, 3, 1, 6, -77879154984857558679020276090075017297715527680000000⟩,
  ⟨7, 1, 3, 3, 2, 6, 280388862823460734533269144119717050947572491878400000⟩,
  ⟨7, 1, 4, 3, 3, 6, 177207510890598167690454491370852141807370764288000000⟩,
  ⟨7, 1, 5, 3, 4, 6, 56601463045337430436229995482960320537712132096000000⟩,
  ⟨7, 1, 6, 3, 5, 6, 12551339255644340490398127627966033227774164992000000⟩,
  ⟨7, 1, 7, 3, 6, 6, -1293688055129558196187375608765212587183413657600000⟩,
  ⟨7, 1, 8, 3, 7, 6, -2734464499736633463176792975596422309454282752000000⟩,
  ⟨7, 1, 2, 4, 0, 6, 298243524852154438348833444127604187384795208089600000⟩,
  ⟨7, 1, 3, 4, 1, 6, -258892647169027338322210017620962740761768283340800000⟩,
  ⟨7, 1, 4, 4, 2, 6, -590793362585776339251730669249075674290153167257600000⟩,
  ⟨7, 1, 5, 4, 3, 6, -5279581118271834746629710021642370464387956736000000⟩,
  ⟨7, 1, 6, 4, 4, 6, -5800467192904827841951138277054691417218088960000000⟩,
  ⟨7, 1, 7, 4, 5, 6, -4454051572199159316392453902462085483779325952000000⟩,
  ⟨7, 1, 8, 4, 6, 6, 3487914156126760501008969406544212284979072204800000⟩,
  ⟨7, 1, 3, 5, 0, 6, 310966268266555723599484108844519554176938881843200000⟩,
  ⟨7, 1, 4, 5, 1, 6, 569598540438180487557430519671925590295045157683200000⟩,
  ⟨7, 1, 5, 5, 2, 6, -410068815871080178408830901906011472677197316096000000⟩,
  ⟨7, 1, 6, 5, 3, 6, -2148644017003695096917573158363367774990893056000000⟩,
  ⟨7, 1, 7, 5, 4, 6, 2822361975466323797897366675133843512626249728000000⟩,
  ⟨7, 1, 8, 5, 5, 6, 1165904297287694966802578737163753078778337689600000⟩,
  ⟨7, 1, 4, 6, 0, 6, 1777160892990091525364647665461730092091693229670400000⟩,
  ⟨7, 1, 5, 6, 1, 6, 523891430299774274423675598949482216074835394560000000⟩,
  ⟨7, 1, 6, 6, 2, 6, -153956730818201316162993740118159115619061989376000000⟩,
  ⟨7, 1, 7, 6, 3, 6, 8462904436087347085415931037486217928312147148800000⟩,
  ⟨7, 1, 8, 6, 4, 6, -1736793053890127618772335819969288216900114841600000⟩,
  ⟨7, 1, 5, 7, 0, 6, 2285701832098769529342727082631522179386649346048000000⟩,
  ⟨7, 1, 6, 7, 1, 6, 305212150411528515980170169257379708099465576448000000⟩,
  ⟨7, 1, 7, 7, 2, 6, -15028525189123321478809635798836091581073929011200000⟩,
  ⟨7, 1, 8, 7, 3, 6, -8318280940711390606706399062098069389941565030400000⟩
]

def collectedFourData_10_2_52 : List CollectedFourTerm := [
  ⟨7, 2, 1, 0, 3, 7, -12268132495297847970776523365050572415611332198400000⟩,
  ⟨7, 2, 2, 0, 4, 7, -22951666104009365387618019715310762208066640281600000⟩,
  ⟨7, 2, 3, 0, 5, 7, 78879695371518663694514383061273607245597245440000000⟩,
  ⟨7, 2, 4, 0, 6, 7, 27596471769372084100040775167160618754787770368000000⟩,
  ⟨7, 2, 5, 0, 7, 7, 89186640616852757590972851594397159325171712000000⟩,
  ⟨7, 2, 6, 0, 8, 7, 1098867926890934584738459643681700086502811238400000⟩,
  ⟨7, 2, 1, 1, 2, 7, -3600304015142282764251616042859169514700931072000000⟩,
  ⟨7, 2, 2, 1, 3, 7, 13703188558367985501504820438381224508365629030400000⟩,
  ⟨7, 2, 3, 1, 4, 7, -75457031587376765631253923054112633358758025625600000⟩,
  ⟨7, 2, 4, 1, 5, 7, -42764068784821756950837403284280041006996809318400000⟩,
  ⟨7, 2, 5, 1, 6, 7, -14715103866973915439726816842948092558525333504000000⟩,
  ⟨7, 2, 6, 1, 7, 7, -3675083229109955118966013434820885153711128576000000⟩,
  ⟨7, 2, 7, 1, 8, 7, -1151480413993541121730739770870667635821065011200000⟩,
  ⟨7, 2, 1, 2, 1, 7, -13188749654015239877475012351310228286367124684800000⟩,
  ⟨7, 2, 2, 2, 2, 7, 3345572849700914313521900037926088042109049241600000⟩,
  ⟨7, 2, 3, 2, 3, 7, 52342922953727767582300569119452732004074153574400000⟩,
  ⟨7, 2, 4, 2, 4, 7, 11401727640629240905900416196963910076363020697600000⟩,
  ⟨7, 2, 5, 2, 5, 7, 2573992927347347369343615009209999185051385856000000⟩,
  ⟨7, 2, 6, 2, 6, 7, 253689591563464726831146050971184067670494412800000⟩,
  ⟨7, 2, 7, 2, 7, 7, 67984722563481697358135067663667691293507584000000⟩,
  ⟨7, 2, 8, 2, 8, 7, 157004630358884030375507586342648291699091046400000⟩,
  ⟨7, 2, 1, 3, 0, 7, -11574964635201817560402662273086340939978794598400000⟩,
  ⟨7, 2, 2, 3, 1, 7, 19173693459114694217255867777099445975342120960000000⟩,
  ⟨7, 2, 3, 3, 2, 7, -34515590893173513234255827791844636836613219942400000⟩,
  ⟨7, 2, 4, 3, 3, 7, -14542712544538584782444733290328537750948544512000000⟩,
  ⟨7, 2, 5, 3, 4, 7, -3483791978674270519976855269522916644516528128000000⟩,
  ⟨7, 2, 6, 3, 5, 7, -618022965030550905534400085862316436215352524800000⟩,
  ⟨7, 2, 7, 3, 6, 7, 53083905454964894999386167422932374007264051200000⟩,
  ⟨7, 2, 8, 3, 7, 7, 96174247878883295640483161640221122800648192000000⟩,
  ⟨7, 2, 2, 4, 0, 7, -73426964157391381562786290654592067299779490611200000⟩,
  ⟨7, 2, 3, 4, 1, 7, 31869428068414646529096234640589008703480188108800000⟩,
  ⟨7, 2, 4, 4, 2, 7, 48484051280481820024814146996563356959556134502400000⟩,
  ⟨7, 2, 5, 4, 3, 7, 324955599396130469932232957223337224881307648000000⟩,
  ⟨7, 2, 6, 4, 4, 7, 285612703163081409494016689707466278488244224000000⟩,
  ⟨7, 2, 7, 4, 5, 7, 182763110173788735503917671331780250906394624000000⟩,
  ⟨7, 2, 8, 4, 6, 7, -122673935121084704384707583597476535232941260800000⟩,
  ⟨7, 2, 3, 5, 0, 7, -38279639173197623669049149411113914769211601715200000⟩,
  ⟨7, 2, 4, 5, 1, 7, -46744676891800308857116333774229142516087442636800000⟩,
  ⟨7, 2, 5, 5, 2, 7, 25239532241274929310703403533462242740171440128000000⟩,
  ⟨7, 2, 6, 5, 3, 7, 105798378893042430220266153578294709737383526400000⟩,
  ⟨7, 2, 7, 5, 4, 7, -115809986550689880217783665929442747048001536000000⟩,
  ⟨7, 2, 8, 5, 5, 7, -41006189292712220276356662940360180950997401600000⟩,
  ⟨7, 2, 4, 6, 0, 7, -145844495429463215804624236647021900628806441369600000⟩,
  ⟨7, 2, 5, 6, 1, 7, -32245257708491159871796809633894037045987246080000000⟩,
  ⟨7, 2, 6, 6, 2, 7, 7580768341026773953702357593021833336538424934400000⟩,
  ⟨7, 2, 7, 6, 3, 7, -347258380548836066314076772302157659867027865600000⟩,
  ⟨7, 2, 8, 6, 4, 7, 61085000626352835293562259042122043619907993600000⟩,
  ⟨7, 2, 5, 7, 0, 7, -140683814160926103885544808376069273268009304064000000⟩,
  ⟨7, 2, 6, 7, 1, 7, -15028525189123321478809635798836091581073929011200000⟩,
  ⟨7, 2, 7, 7, 2, 7, 616665514614407368557105514634102561124542054400000⟩,
  ⟨7, 2, 8, 7, 3, 7, 292563466519758888856303583933015584605103718400000⟩
]

def collectedFourData_10_2_53 : List CollectedFourTerm := [
  ⟨7, 3, 0, 0, 2, 8, -19305415248362306533418426668214241592757295513600000⟩,
  ⟨7, 3, 1, 0, 3, 8, -40742430050667332915479222317224372342837005516800000⟩,
  ⟨7, 3, 2, 0, 4, 8, -38111206051421573978268677444328367324137101721600000⟩,
  ⟨7, 3, 3, 0, 5, 8, 87319741406548471080550324897133367739243560960000000⟩,
  ⟨7, 3, 4, 0, 6, 8, 22911949335805587751084334528308298276388470784000000⟩,
  ⟨7, 3, 5, 0, 7, 8, 59237711496494729492095846053938958533709004800000⟩,
  ⟨7, 3, 6, 0, 8, 8, 608222830755964207026707224643987583452105932800000⟩,
  ⟨7, 3, 0, 1, 1, 8, 142236766439996148285686545693173527430820999987200000⟩,
  ⟨7, 3, 1, 1, 2, 8, -11956598492418706886204199461846942175140511744000000⟩,
  ⟨7, 3, 2, 1, 3, 8, 22754123397526040546116063946773320381980108390400000⟩,
  ⟨7, 3, 3, 1, 4, 8, -83530856128211789135995365520355905796236011110400000⟩,
  ⟨7, 3, 4, 1, 5, 8, -35504835023083654606593007876176910101039493939200000⟩,
  ⟨7, 3, 5, 1, 6, 8, -9773762880671165280539595891239479459050002841600000⟩,
  ⟨7, 3, 6, 1, 7, 8, -2034156671764324599124242235876437396125908992000000⟩,
  ⟨7, 3, 7, 1, 8, 8, -546294698769080160329421881155662491621208883200000⟩,
  ⟨7, 3, 0, 2, 0, 8, 22870466887377015041055879703927084402818731212800000⟩,
  ⟨7, 3, 1, 2, 1, 8, -43799796785731830206083987994836001575602330009600000⟩,
  ⟨7, 3, 2, 2, 2, 8, 5555318540152512226965705542411589664072374681600000⟩,
  ⟨7, 3, 3, 2, 3, 8, 57943561714523418614123492848644088327956961689600000⟩,
  ⟨7, 3, 4, 2, 4, 8, 9466275552394478151680555616351156115402968268800000⟩,
  ⟨7, 3, 5, 2, 5, 8, 1709644509195784842460611256114570598990374502400000⟩,
  ⟨7, 3, 6, 2, 6, 8, 140417058081420858891875208708866716003309977600000⟩,
  ⟨7, 3, 7, 2, 7, 8, 32253864748693020150656731604339010645786624000000⟩,
  ⟨7, 3, 8, 2, 8, 8, 65176486442409545067474454807714303816866201600000⟩,
  ⟨7, 3, 1, 3, 0, 8, -38440421732436528667874095252827610246028250316800000⟩,
  ⟨7, 3, 2, 3, 1, 8, 31837888320424130696925881130106618645535784960000000⟩,
  ⟨7, 3, 3, 3, 2, 8, -38208723513584537167602534334009121748740053401600000⟩,
  ⟨7, 3, 4, 3, 3, 8, -12074075838761975215278350176154359334128582656000000⟩,
  ⟨7, 3, 5, 3, 4, 8, -2313932475975699135788795393760613523302593331200000⟩,
  ⟨7, 3, 6, 3, 5, 8, -342075392378236682875991381637167066971216281600000⟩,
  ⟨7, 3, 7, 3, 6, 8, 25184497962436938192784113834364333072790323200000⟩,
  ⟨7, 3, 8, 3, 7, 8, 39924297446889173189344267644774167240245248000000⟩,
  ⟨7, 3, 2, 4, 0, 8, -121925360366054040628380472646757481384143696691200000⟩,
  ⟨7, 3, 3, 4, 1, 8, 35279423996271791009659744836052034912653620019200000⟩,
  ⟨7, 3, 4, 4, 2, 8, 40253846064694795678591343762695309024864449331200000⟩,
  ⟨7, 3, 5, 4, 3, 8, 215835307990747143245604433558096873992172339200000⟩,
  ⟨7, 3, 6, 4, 4, 8, 158086483886387990900546654605912440840388608000000⟩,
  ⟨7, 3, 7, 4, 5, 8, 86707960469964331511701375520733121493336064000000⟩,
  ⟨7, 3, 8, 4, 6, 8, -50924969862227928805617878372722546998194995200000⟩,
  ⟨7, 3, 3, 5, 0, 8, -42375521076701709561637230405631628368975547596800000⟩,
  ⟨7, 3, 4, 5, 1, 8, -38809731824203414837098986178620131725906699878400000⟩,
  ⟨7, 3, 5, 5, 2, 8, 16764081692887536137180231484843275345556878131200000⟩,
  ⟨7, 3, 6, 5, 3, 8, 58559348148219382370296811987306597023796428800000⟩,
  ⟨7, 3, 7, 5, 4, 8, -54943515276774153021973147363659267698589696000000⟩,
  ⟨7, 3, 8, 5, 5, 8, -17022678467394050867453311090856154922116710400000⟩,
  ⟨7, 3, 4, 6, 0, 8, -121087279493991033257359627927270695396803661004800000⟩,
  ⟨7, 3, 5, 6, 1, 8, -21417280212085730766366737760495431668551647232000000⟩,
  ⟨7, 3, 6, 6, 2, 8, 4195951366721555306343310143872107626160245964800000⟩,
  ⟨7, 3, 7, 6, 3, 8, -164749143877343534869764083734364472141781401600000⟩,
  ⟨7, 3, 8, 6, 4, 8, 25357887255028869901670026023577577616467558400000⟩,
  ⟨7, 3, 5, 7, 0, 8, -93442102290784828500151889628044154440406112665600000⟩,
  ⟨7, 3, 6, 7, 1, 8, -8318280940711390606706399062098069389941565030400000⟩,
  ⟨7, 3, 7, 7, 2, 8, 292563466519758888856303583933015584605103718400000⟩,
  ⟨7, 3, 8, 7, 3, 8, 121450295864413886387742539078094695956060569600000⟩
]

def collectedFourData_10_2 : List (List CollectedFourTerm) := [
  collectedFourData_10_2_0,
  collectedFourData_10_2_1,
  collectedFourData_10_2_2,
  collectedFourData_10_2_3,
  collectedFourData_10_2_4,
  collectedFourData_10_2_5,
  collectedFourData_10_2_6,
  collectedFourData_10_2_7,
  collectedFourData_10_2_8,
  collectedFourData_10_2_9,
  collectedFourData_10_2_10,
  collectedFourData_10_2_11,
  collectedFourData_10_2_12,
  collectedFourData_10_2_13,
  collectedFourData_10_2_14,
  collectedFourData_10_2_15,
  collectedFourData_10_2_16,
  collectedFourData_10_2_17,
  collectedFourData_10_2_18,
  collectedFourData_10_2_19,
  collectedFourData_10_2_20,
  collectedFourData_10_2_21,
  collectedFourData_10_2_22,
  collectedFourData_10_2_23,
  collectedFourData_10_2_24,
  collectedFourData_10_2_25,
  collectedFourData_10_2_26,
  collectedFourData_10_2_27,
  collectedFourData_10_2_28,
  collectedFourData_10_2_29,
  collectedFourData_10_2_30,
  collectedFourData_10_2_31,
  collectedFourData_10_2_32,
  collectedFourData_10_2_33,
  collectedFourData_10_2_34,
  collectedFourData_10_2_35,
  collectedFourData_10_2_36,
  collectedFourData_10_2_37,
  collectedFourData_10_2_38,
  collectedFourData_10_2_39,
  collectedFourData_10_2_40,
  collectedFourData_10_2_41,
  collectedFourData_10_2_42,
  collectedFourData_10_2_43,
  collectedFourData_10_2_44,
  collectedFourData_10_2_45,
  collectedFourData_10_2_46,
  collectedFourData_10_2_47,
  collectedFourData_10_2_48,
  collectedFourData_10_2_49,
  collectedFourData_10_2_50,
  collectedFourData_10_2_51,
  collectedFourData_10_2_52,
  collectedFourData_10_2_53
]

def collectedFourData_10_3_0 : List CollectedFourTerm := [
  ⟨0, 3, 7, 2, 8, 0, 33594811991758933568905936798481115232605516595200000⟩,
  ⟨0, 3, 7, 3, 7, 0, -18758641415859994034370653273875794453934689484800000⟩,
  ⟨0, 3, 8, 3, 8, 0, -84885611736805918588385660890005403080012595200000000⟩,
  ⟨0, 3, 7, 4, 6, 0, 6160813201129171472566306472872648288977813504000000⟩,
  ⟨0, 3, 8, 4, 7, 0, -30153615520174904903311449035998227125391222374400000⟩,
  ⟨0, 3, 7, 5, 5, 0, 16316555840960566800422264219249342846847890227200000⟩,
  ⟨0, 3, 8, 5, 6, 0, -62787741534275616650945660052133779629588191641600000⟩,
  ⟨0, 3, 7, 6, 4, 0, -5841091707999553272203905834242560784758892134400000⟩,
  ⟨0, 3, 8, 6, 5, 0, 65892933646157854939917283685909050594444915507200000⟩,
  ⟨0, 3, 7, 7, 3, 0, -244739193924325927987447259472941140439939520921600000⟩,
  ⟨0, 3, 8, 7, 4, 0, -130284941275600969045107244457989411887768403968000000⟩
]

def collectedFourData_10_3_1 : List CollectedFourTerm := [
  ⟨0, 4, 6, 1, 8, 1, -148162107323847065951276968648774306165161984000000⟩,
  ⟨0, 4, 6, 2, 7, 1, -198257846122968067666810047619553801143320576000000⟩,
  ⟨0, 4, 7, 2, 8, 1, -929790988446526592902270314628075515820376064000000⟩,
  ⟨0, 4, 6, 3, 6, 1, 525325323911452675495800683308782892785598464000000⟩,
  ⟨0, 4, 7, 3, 7, 1, 519175870019602365866598049636661474975809536000000⟩,
  ⟨0, 4, 8, 3, 8, 1, 1174673590389700352993643468782172773548032000000000⟩,
  ⟨0, 4, 6, 4, 5, 1, -417949487709421813544999555483580728120180736000000⟩,
  ⟨0, 4, 7, 4, 6, 1, -170510512078992745801025028747636566686433280000000⟩,
  ⟨0, 4, 8, 4, 7, 1, 417275143355729067893614642962564880483221504000000⟩,
  ⟨0, 4, 6, 5, 4, 1, -471397329771423334425634804481032524172099584000000⟩,
  ⟨0, 4, 7, 5, 5, 1, -451587185162138497882361548596735511105634304000000⟩,
  ⟨0, 4, 8, 5, 6, 1, 868876365163170037459279865098099218035245056000000⟩,
  ⟨0, 4, 6, 6, 3, 1, 1745484983078964334360290884814777997930266624000000⟩,
  ⟨0, 4, 7, 6, 4, 1, 161661700447080332894015412167433112894046208000000⟩,
  ⟨0, 4, 8, 6, 5, 1, -911846982824783847976349333513348834710781952000000⟩,
  ⟨0, 4, 6, 7, 2, 1, -1722579901411559006665734181722674435337486336000000⟩,
  ⟨0, 4, 7, 7, 3, 1, 6773554710957348848321948303121094404275699712000000⟩,
  ⟨0, 4, 8, 7, 4, 1, 1802923682949241149485061621739582852568186880000000⟩
]

def collectedFourData_10_3_2 : List CollectedFourTerm := [
  ⟨0, 5, 5, 0, 8, 2, -841072263728580026708948695330462129541087232000000⟩,
  ⟨0, 5, 5, 1, 7, 2, 6670995361985278601957511995033851257189040128000000⟩,
  ⟨0, 5, 6, 1, 8, 2, 3648957292767572064238941888907412916305657856000000⟩,
  ⟨0, 5, 5, 2, 6, 2, 4662678893273769994379737596261845026077671424000000⟩,
  ⟨0, 5, 6, 2, 7, 2, 4882722219099787632512236702580313038398685184000000⟩,
  ⟨0, 5, 7, 2, 8, 2, 11449511853343651865709169655076996485153292288000000⟩,
  ⟨0, 5, 5, 3, 5, 2, -1761838728463069523488898964768191685643468800000000⟩,
  ⟨0, 5, 6, 3, 6, 2, -12937786228784652311527062006586303816113586176000000⟩,
  ⟨0, 5, 7, 3, 7, 2, -6393168305159697595978563019699462102069542912000000⟩,
  ⟨0, 5, 8, 3, 8, 2, -9643342331124427331113167713756062307844096000000000⟩,
  ⟨0, 5, 5, 4, 4, 2, 6347213985350083409995485689470426073763151872000000⟩,
  ⟨0, 5, 6, 4, 5, 2, 10293318978328948201547875646781503596998426624000000⟩,
  ⟨0, 5, 7, 4, 6, 2, 2099678479816112277877140326637007282120949760000000⟩,
  ⟨0, 5, 8, 4, 7, 2, -3425570376800052139735035953524859023248064512000000⟩,
  ⟨0, 5, 5, 5, 3, 2, -16553898964592293689392062044660575509785083904000000⟩,
  ⟨0, 5, 6, 5, 4, 2, 11609639976980399229642424020811873833248096256000000⟩,
  ⟨0, 5, 7, 5, 5, 2, 5560876469636119998085003159978540844992954368000000⟩,
  ⟨0, 5, 8, 5, 6, 2, -7132936588718075635855389778743825341683335168000000⟩,
  ⟨0, 5, 5, 6, 2, 2, -244996456555910556867378916501551114004463616000000⟩,
  ⟨0, 5, 6, 6, 3, 2, -42988050544534406435103160768086869008623599616000000⟩,
  ⟨0, 5, 7, 6, 4, 2, -1990713588860500398189965178013550071498407936000000⟩,
  ⟨0, 5, 8, 6, 5, 2, 7485698734458776147635382946612014146551545856000000⟩,
  ⟨0, 5, 5, 7, 1, 2, 11420891811001795755134042955241607401436086272000000⟩,
  ⟨0, 5, 6, 7, 2, 2, 42423940960097744392811153226807061875234177024000000⟩,
  ⟨0, 5, 7, 7, 3, 2, -83410030766111385969204955996123238196213448704000000⟩,
  ⟨0, 5, 8, 7, 4, 2, -14800886317537165759096932905451634370952560640000000⟩
]

def collectedFourData_10_3_3 : List CollectedFourTerm := [
  ⟨0, 6, 4, 0, 7, 3, -1432103551901070876753730022195934380665885163520000⟩,
  ⟨0, 6, 5, 0, 8, 3, -135000882856054810335128030481387264435604684800000⟩,
  ⟨0, 6, 4, 1, 6, 3, -3208677178447063475818341603580998767456896942080000⟩,
  ⟨0, 6, 5, 1, 7, 3, 1070764430400104603533830993639283472758682419200000⟩,
  ⟨0, 6, 6, 1, 8, 3, 292847878399799080474239116990983199364690739200000⟩,
  ⟨0, 6, 4, 2, 5, 3, 407164318151138842807129738632462796568804720640000⟩,
  ⟨0, 6, 5, 2, 6, 3, 748408661433858162797115735568779819397781913600000⟩,
  ⟨0, 6, 6, 2, 7, 3, 391863956728970097705322428928762746795510988800000⟩,
  ⟨0, 6, 7, 2, 8, 3, 612588745395074166800397765302449152652109414400000⟩,
  ⟨0, 6, 4, 3, 4, 3, -279355392552228410228541361311164837384568176640000⟩,
  ⟨0, 6, 5, 3, 5, 3, -282793517334747371428879717739385812491960320000000⟩,
  ⟨0, 6, 6, 3, 6, 3, -1038324908816919579454359588786445876118893363200000⟩,
  ⟨0, 6, 7, 3, 7, 3, -342056762010654025027306544929480794518952345600000⟩,
  ⟨0, 6, 8, 3, 8, 3, -386964290860589679863852985379830611155353600000000⟩,
  ⟨0, 6, 4, 4, 3, 3, -624399981092570295947141149314506558022667468800000⟩,
  ⟨0, 6, 5, 4, 4, 3, 1018794137735447285135455006908872246973746380800000⟩,
  ⟨0, 6, 6, 4, 5, 3, 826092601979934142129965758808693004080827596800000⟩,
  ⟨0, 6, 7, 4, 6, 3, 112340108657816932443128095668669496833343488000000⟩,
  ⟨0, 6, 8, 4, 7, 3, -137459955908970767688109894405636462140928819200000⟩,
  ⟨0, 6, 4, 5, 2, 3, 4278177307592058975824838930031306611558218465280000⟩,
  ⟨0, 6, 5, 5, 3, 3, -2657073679998409891887023981594344178335717785600000⟩,
  ⟨0, 6, 6, 5, 4, 3, 931734236238638053754333562297394888944333619200000⟩,
  ⟨0, 6, 7, 5, 5, 3, 297526251203151144761237188660709561716860518400000⟩,
  ⟨0, 6, 8, 5, 6, 3, -286227705501874629496950888382010375231294668800000⟩,
  ⟨0, 6, 4, 6, 1, 3, -2295696080762564403615548413374587481056681656320000⟩,
  ⟨0, 6, 5, 6, 2, 3, -39324490127671663061870520023181106098890342400000⟩,
  ⟨0, 6, 6, 6, 3, 3, -3450015549226135734344605575088786602544280371200000⟩,
  ⟨0, 6, 7, 6, 4, 3, -106510107632653938111228298495056594533665996800000⟩,
  ⟨0, 6, 8, 6, 5, 3, 300383207700363244818879822125747899570166169600000⟩,
  ⟨0, 6, 4, 7, 0, 3, -43804710695013649040193559651143610563646917181440000⟩,
  ⟨0, 6, 5, 7, 1, 3, 1833172420469079590352203595404265546507406540800000⟩,
  ⟨0, 6, 6, 7, 2, 3, 3404742809171134096606864504211393300730268876800000⟩,
  ⟨0, 6, 7, 7, 3, 3, -4462727036301980445369031303544040512810070835200000⟩,
  ⟨0, 6, 8, 7, 4, 3, -593924210228275625231420272391334551328129024000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1010. -/
namespace LaughlinFock
def collectedFourData_10_3_4 : List CollectedFourTerm := [
  ⟨0, 7, 3, 0, 6, 4, -1432103551901070876753730022195934380665885163520000⟩,
  ⟨0, 7, 4, 0, 7, 4, 20544862290599082900808836194710801404751113093120000⟩,
  ⟨0, 7, 5, 0, 8, 4, 968356842528989858403155440338202499496699494400000⟩,
  ⟨0, 7, 3, 1, 5, 4, 19199392951462349440685317852690423453146949877760000⟩,
  ⟨0, 7, 4, 1, 6, 4, 46031469357557177333696345540067082359835962900480000⟩,
  ⟨0, 7, 5, 1, 7, 4, -7680557645094639430790238818322909838282693017600000⟩,
  ⟨0, 7, 6, 1, 8, 4, -1400392060995692697154290285220228491156809318400000⟩,
  ⟨0, 7, 3, 2, 4, 4, -25001735662699013394886274677938411189436541829120000⟩,
  ⟨0, 7, 4, 2, 5, 4, -5841152223214847651712911324067732340583788707840000⟩,
  ⟨0, 7, 5, 2, 6, 4, -5368310436015304715702216455595588736999279820800000⟩,
  ⟨0, 7, 6, 2, 7, 4, -1873884752015966378374430740985635562919139737600000⟩,
  ⟨0, 7, 7, 2, 8, 4, -2197039347854027693509940321225759618825296281600000⟩,
  ⟨0, 7, 3, 3, 3, 4, 33418364528820434026706817323823756008200140226560000⟩,
  ⟨0, 7, 4, 3, 4, 4, 4007613878551605664205826706428621725227643043840000⟩,
  ⟨0, 7, 5, 3, 5, 4, 2028468493987046042158789697292195117095976960000000⟩,
  ⟨0, 7, 6, 3, 6, 4, 4965246690488874365426047425483780299147339366400000⟩,
  ⟨0, 7, 7, 3, 7, 4, 1226780888460949827511099969427930954678560358400000⟩,
  ⟨0, 7, 8, 3, 8, 4, 1110272795086166481596233328713753598172856320000000⟩,
  ⟨0, 7, 3, 4, 2, 4, -45748225108991283582428990812933780362215030784000000⟩,
  ⟨0, 7, 4, 4, 3, 4, 8957600593037070686195675972035029531710246092800000⟩,
  ⟨0, 7, 5, 4, 4, 4, -7307776464369213054302731652623072723523233382400000⟩,
  ⟨0, 7, 6, 4, 5, 4, -3950356505163494900299491581811597621260294553600000⟩,
  ⟨0, 7, 7, 4, 6, 4, -402905931456907518627050237832186648625938432000000⟩,
  ⟨0, 7, 8, 4, 7, 4, 394398276699018128758494783563476226297340887040000⟩,
  ⟨0, 7, 3, 5, 1, 4, 37990346931906223490198113172669181284582298746880000⟩,
  ⟨0, 7, 4, 5, 2, 4, -61374447066043256532230714351577877876261445959680000⟩,
  ⟨0, 7, 5, 5, 3, 4, 19059101131017118790435059560012521394381049036800000⟩,
  ⟨0, 7, 6, 5, 4, 4, -4455532457725905703099956697990030178436671078400000⟩,
  ⟨0, 7, 7, 5, 5, 4, -1067072952003471523255303939899378199290288537600000⟩,
  ⟨0, 7, 8, 5, 6, 4, 821240724594807352067097882161317921115665858560000⟩,
  ⟨0, 7, 3, 6, 0, 4, 20689562349390852969835001772698012048498444206080000⟩,
  ⟨0, 7, 4, 6, 1, 4, 32933903262599434081860699114889533147752347729920000⟩,
  ⟨0, 7, 5, 6, 2, 4, 282073259733402290351001559559096344518013747200000⟩,
  ⟨0, 7, 6, 6, 3, 4, 16497897856893914462127531670521321075142714982400000⟩,
  ⟨0, 7, 7, 6, 4, 4, 381996729734548527987612435015228971470238515200000⟩,
  ⟨0, 7, 8, 6, 5, 4, -861855503175052237797290588253858742582923755520000⟩,
  ⟨0, 7, 4, 7, 0, 4, 628419465697098731255525434860159315812092099952640000⟩,
  ⟨0, 7, 5, 7, 1, 4, -13149284799784902031752469697321382216238261862400000⟩,
  ⟨0, 7, 6, 7, 2, 4, -16281404617813683887553613062347406803199433113600000⟩,
  ⟨0, 7, 7, 7, 3, 4, 16005496299420393000131623802773844134747491532800000⟩,
  ⟨0, 7, 8, 7, 4, 4, 1704079442299387223237707148487485528210197708800000⟩
]

def collectedFourData_10_3_5 : List CollectedFourTerm := [
  ⟨0, 8, 2, 0, 5, 5, -841072263728580026708948695330462129541087232000000⟩,
  ⟨0, 8, 3, 0, 6, 5, -135000882856054810335128030481387264435604684800000⟩,
  ⟨0, 8, 4, 0, 7, 5, 968356842528989858403155440338202499496699494400000⟩,
  ⟨0, 8, 5, 0, 8, 5, 30428206695802302349263581794647069689905152000000⟩,
  ⟨0, 8, 2, 1, 4, 5, 2898793013757856493301143080724443012330527129600000⟩,
  ⟨0, 8, 3, 1, 5, 5, 1809879596560614394431356399484804321826465382400000⟩,
  ⟨0, 8, 4, 1, 6, 5, 2169636753635024012359364257116405271801469337600000⟩,
  ⟨0, 8, 5, 1, 7, 5, -241342432148888118115638668351352162440183808000000⟩,
  ⟨0, 8, 6, 1, 8, 5, -33002879632563130510600367410677015908450304000000⟩,
  ⟨0, 8, 2, 2, 3, 5, -1080362355303015213292202569289664457405051699200000⟩,
  ⟨0, 8, 3, 2, 4, 5, -2356852186364271171110358116432408321110887628800000⟩,
  ⟨0, 8, 4, 2, 5, 5, -275315533567325868822179555458572315599359180800000⟩,
  ⟨0, 8, 5, 2, 6, 5, -168685811242580334598753792033931223172644864000000⟩,
  ⟨0, 8, 6, 2, 7, 5, -44161627760233758501564461231489622585901056000000⟩,
  ⟨0, 8, 7, 2, 8, 5, -41421900146264536242918715587732181086948556800000⟩,
  ⟨0, 8, 2, 3, 2, 5, -577701285593031941679721595974608392716025856000000⟩,
  ⟨0, 8, 3, 3, 3, 5, 3150267108134285169803884380219374125149742694400000⟩,
  ⟨0, 8, 4, 3, 4, 5, 188893956387596129943748694208735541870775500800000⟩,
  ⟨0, 8, 5, 3, 5, 5, 63739580183854429940908680437002022997196800000000⟩,
  ⟨0, 8, 6, 3, 6, 5, 117015401212482868104486063147880141956317184000000⟩,
  ⟨0, 8, 7, 3, 7, 5, 23129123978962695827376862010442049622586163200000⟩,
  ⟨0, 8, 8, 3, 8, 5, 17443781369571229629212453428250628902092800000000⟩,
  ⟨0, 8, 2, 4, 1, 5, -1333587209810654255606524636950853960063569100800000⟩,
  ⟨0, 8, 3, 4, 2, 5, -4312572767948833790515747869141092180070236160000000⟩,
  ⟨0, 8, 4, 4, 3, 5, 422205498592137252681672776956809115846311936000000⟩,
  ⟨0, 8, 5, 4, 4, 5, -229628710180657250885936541811765392747528192000000⟩,
  ⟨0, 8, 6, 4, 5, 5, -93097600219846272399848925211507179720278016000000⟩,
  ⟨0, 8, 7, 4, 6, 5, -7596190426651639648740435833172561059905536000000⟩,
  ⟨0, 8, 8, 4, 7, 5, 6196492737390184597807748968978247310743961600000⟩,
  ⟨0, 8, 2, 5, 0, 5, 9949994396324421157848572371667337577668123033600000⟩,
  ⟨0, 8, 3, 5, 1, 5, 3581256654944351350102700642664784227541922611200000⟩,
  ⟨0, 8, 4, 5, 2, 5, -2892809157452047389335518830595484796501727641600000⟩,
  ⟨0, 8, 5, 5, 3, 5, 598884877124650193157858386035570147426566144000000⟩,
  ⟨0, 8, 6, 5, 4, 5, -105003024150790669513970292302139473635835904000000⟩,
  ⟨0, 8, 7, 5, 5, 5, -20118069032236653637775778725874094922583244800000⟩,
  ⟨0, 8, 8, 5, 6, 5, 12902724190867250106946092097567103891433062400000⟩,
  ⟨0, 8, 3, 6, 0, 5, 1950354204041596789510755352650894153434215219200000⟩,
  ⟨0, 8, 4, 6, 1, 5, 1552299067495770967942821475904967796620420710400000⟩,
  ⟨0, 8, 5, 6, 2, 5, 8863451027114256524805709475515553154072576000000⟩,
  ⟨0, 8, 6, 6, 3, 5, 388804073035276788048781078552535480238342144000000⟩,
  ⟨0, 8, 7, 6, 4, 5, 7201978613045468142350134220998688678451609600000⟩,
  ⟨0, 8, 8, 6, 5, 5, -13540833420475413879775804815007785524448460800000⟩,
  ⟨0, 8, 4, 7, 0, 5, 29619779435788696968286758682718525568368561356800000⟩,
  ⟨0, 8, 5, 7, 1, 5, -413183589166251240594766346187590074569326592000000⟩,
  ⟨0, 8, 6, 7, 2, 5, -383702001615685572472417829933001384306671616000000⟩,
  ⟨0, 8, 7, 7, 3, 5, 301759761450593118266473958845992022745441894400000⟩,
  ⟨0, 8, 8, 7, 4, 5, 26773230290258915132408059852381807498493952000000⟩
]

def collectedFourData_10_3_6 : List CollectedFourTerm := [
  ⟨1, 2, 7, 2, 8, 0, -13140689032699289464156826665601664014690864332800000⟩,
  ⟨1, 2, 7, 3, 7, 0, 7337486323251304605788679354088548509204820787200000⟩,
  ⟨1, 2, 8, 3, 8, 0, 33203204931090117028054315511679952693808332800000000⟩,
  ⟨1, 2, 7, 4, 6, 0, -2409816446790848621856663760226268714218029056000000⟩,
  ⟨1, 2, 8, 4, 7, 0, 11794657010117931458477368938219558803101817241600000⟩,
  ⟨1, 2, 7, 5, 5, 0, -6382258857210829794565761012587973176009215180800000⟩,
  ⟨1, 2, 8, 5, 6, 0, 24559571482936422267620414842482468066324538982400000⟩,
  ⟨1, 2, 7, 6, 4, 0, 2284756639362331346857832112656831919330793881600000⟩,
  ⟨1, 2, 8, 6, 5, 0, -25774174616868081084513565981299759812172369100800000⟩,
  ⟨1, 2, 7, 7, 3, 0, 95730306282469272732295576742557410237687948902400000⟩,
  ⟨1, 2, 8, 7, 4, 0, 50961258523075995984521619583782251530448535552000000⟩
]

def collectedFourData_10_3_7 : List CollectedFourTerm := [
  ⟨1, 3, 6, 1, 8, 1, 598380889539468812518549160720901295774787174400000⟩,
  ⟨1, 3, 6, 2, 7, 1, 800702071967265852677253833223395095034304921600000⟩,
  ⟨1, 3, 7, 2, 8, 1, 3755137995819161304600665644640666943878489702400000⟩,
  ⟨1, 3, 6, 3, 6, 1, -2121626374634792156747049428727088136283645542400000⟩,
  ⟨1, 3, 7, 3, 7, 1, -2096790633861043880210885476445880197670607257600000⟩,
  ⟨1, 3, 8, 3, 8, 1, -4744143024366774978962636550340284840620851200000000⟩,
  ⟨1, 3, 6, 4, 5, 1, 1687968609217236838968057190832093699252001177600000⟩,
  ⟨1, 3, 7, 4, 6, 1, 688639178643998653631431478522883081920053248000000⟩,
  ⟨1, 3, 8, 4, 7, 1, -1685245141108507822531904344383578206399522406400000⟩,
  ⟨1, 3, 6, 5, 4, 1, 1903827899117319789194362557810556414045087334400000⟩,
  ⟨1, 3, 7, 5, 5, 1, 1823820857051568608261566743734723670972982886400000⟩,
  ⟨1, 3, 8, 5, 6, 1, -3509122687825564815284975885745834096873544089600000⟩,
  ⟨1, 3, 6, 6, 3, 1, -7049473551085663358338656713391747359905834598400000⟩,
  ⟨1, 3, 7, 6, 4, 1, -652901567514471265091428755511696913777609932800000⟩,
  ⟨1, 3, 8, 6, 5, 1, 3682667711481409791042445552062977512500835123200000⟩,
  ⟨1, 3, 6, 7, 2, 1, 6956967016245697768299374499971871770114890137600000⟩,
  ⟨1, 3, 7, 7, 3, 1, -27356290798616028394830284224880998817358623539200000⟩,
  ⟨1, 3, 8, 7, 4, 1, -7281450680347477243334487618436954183862059008000000⟩
]

def collectedFourData_10_3_8 : List CollectedFourTerm := [
  ⟨1, 4, 5, 0, 8, 2, 2898793013757856493301143080724443012330527129600000⟩,
  ⟨1, 4, 5, 1, 7, 2, -22991882605196031924658129995749099448144651878400000⟩,
  ⟨1, 4, 6, 1, 8, 2, -12576293814378923143388113953205544649466105036800000⟩,
  ⟨1, 4, 5, 2, 6, 2, -16070130456210089708214417331465546828252132147200000⟩,
  ⟨1, 4, 6, 2, 7, 2, -16828519578211080578549204818231542068527969075200000⟩,
  ⟨1, 4, 7, 2, 8, 2, -39461252501985867078274599242519954171831412326400000⟩,
  ⟨1, 4, 5, 3, 5, 2, 6072255640431988549655124949604619430542704640000000⟩,
  ⟨1, 4, 6, 3, 6, 2, 44590656416648105849740133776677487341074173132800000⟩,
  ⟨1, 4, 7, 3, 7, 2, 22034339280929667099762772414620856694722894233600000⟩,
  ⟨1, 4, 8, 3, 8, 2, 33236208806619097940452209303286264783228108800000000⟩,
  ⟨1, 4, 5, 4, 4, 2, -21875955671148555179333411720785338158810765721600000⟩,
  ⟨1, 4, 6, 4, 5, 2, -35476382267659834298356719470542750503893414707200000⟩,
  ⟨1, 4, 7, 4, 6, 2, -7236635389028629470670917180043617296845897728000000⟩,
  ⟨1, 4, 8, 4, 7, 2, 11806380860049793262135533939487647402131298713600000⟩,
  ⟨1, 4, 5, 5, 3, 2, 57053750002745403172777216090447331839968490291200000⟩,
  ⟨1, 4, 6, 5, 4, 2, -40013141211341941107161113068353243152642788556800000⟩,
  ⟨1, 4, 7, 5, 5, 2, -19165808404013214313956171739210396145990133350400000⟩,
  ⟨1, 4, 8, 5, 6, 2, 24583983615498630646075752715359141414998271590400000⟩,
  ⟨1, 4, 5, 6, 2, 2, 844391198339276538118264038088561132993039564800000⟩,
  ⟨1, 4, 6, 6, 3, 2, 148160230657397592889282668424860018631984860364800000⟩,
  ⟨1, 4, 7, 6, 4, 2, 6861083039642219590473759299671971459079392460800000⟩,
  ⟨1, 4, 8, 6, 5, 2, -25799794060915207448845878197330679295772511436800000⟩,
  ⟨1, 4, 5, 7, 1, 2, -39362612251472506350124822834670810359473478041600000⟩,
  ⟨1, 4, 6, 7, 2, 2, -146216001852241623424209163678016873434801451827200000⟩,
  ⟨1, 4, 7, 7, 3, 2, 287476385667805577725705321128757753459445543731200000⟩,
  ⟨1, 4, 8, 7, 4, 2, 51011913844951895317728453033635246328766267392000000⟩
]

def collectedFourData_10_3_9 : List CollectedFourTerm := [
  ⟨1, 5, 4, 0, 7, 3, 19199392951462349440685317852690423453146949877760000⟩,
  ⟨1, 5, 5, 0, 8, 3, 1809879596560614394431356399484804321826465382400000⟩,
  ⟨1, 5, 4, 1, 6, 3, 43016899107342116163212742009355668870489220055040000⟩,
  ⟨1, 5, 5, 1, 7, 3, -14355126087363063678906224543827239394921257369600000⟩,
  ⟨1, 5, 6, 1, 8, 3, -3926043954668025126523143739460260977662597529600000⟩,
  ⟨1, 5, 4, 2, 5, 3, -5458619056995373644196949059497214636812738232320000⟩,
  ⟨1, 5, 5, 2, 6, 3, -10033486726621282994015279745080199749489708236800000⟩,
  ⟨1, 5, 6, 2, 7, 3, -5253495865412153752227305664414668056433157734400000⟩,
  ⟨1, 5, 7, 2, 8, 3, -8212626820784408404932362965705803718812971827200000⟩,
  ⟨1, 5, 4, 3, 4, 3, 3745157916549010163537227400389990800179928760320000⟩,
  ⟨1, 5, 5, 3, 5, 3, 3791250888407167040769499753858705752493916160000000⟩,
  ⟨1, 5, 6, 3, 6, 3, 13920227981561816846715814366708504647247174041600000⟩,
  ⟨1, 5, 7, 3, 7, 3, 4585759302691157891102672344387562776080207052800000⟩,
  ⟨1, 5, 8, 3, 8, 3, 5187808848427224156253008669092067301706956800000000⟩,
  ⟨1, 5, 4, 4, 3, 3, 8370973300057879787867644276998430365575439974400000⟩,
  ⟨1, 5, 5, 4, 4, 3, -13658390108078107166907508974141587536059197030400000⟩,
  ⟨1, 5, 6, 4, 5, 3, -11074950871153467290620004403282350466828494438400000⟩,
  ⟨1, 5, 7, 4, 6, 3, -1506079562101665676770383614911331790323974144000000⟩,
  ⟨1, 5, 8, 4, 7, 3, 1842846982038160551086578564404938985963100569600000⟩,
  ⟨1, 5, 4, 5, 2, 3, -57355075431139797979826419509962665073561976176640000⟩,
  ⟨1, 5, 5, 5, 3, 3, 35621866600049908353589412681239013443515501772800000⟩,
  ⟨1, 5, 6, 5, 4, 3, -12491227819475451746197282078507411008283842969600000⟩,
  ⟨1, 5, 7, 5, 5, 3, -3988764222141529470127315022839613625403126579200000⟩,
  ⟨1, 5, 8, 5, 6, 3, 3837291084315076638402855068461507126854313574400000⟩,
  ⟨1, 5, 4, 6, 1, 3, 30777083886973886535964095241515226631128649564160000⟩,
  ⟨1, 5, 5, 6, 2, 3, 527200939886521279018426224445954897636176691200000⟩,
  ⟨1, 5, 6, 6, 3, 3, 46252384564173949158299708030469851884998465945600000⟩,
  ⟨1, 5, 7, 6, 4, 3, 1427920073955053696053202617025010728287233638400000⟩,
  ⟨1, 5, 8, 6, 5, 3, -4027065803310289603948371458932496862811049164800000⟩,
  ⟨1, 5, 4, 7, 0, 3, 587264693703371269190082751381164865700210902302720000⟩,
  ⟨1, 5, 5, 7, 1, 3, -24576293803369138101516098464892463311413995110400000⟩,
  ⟨1, 5, 6, 7, 2, 3, -45645438840764815242407359210574825863824959078400000⟩,
  ⟨1, 5, 7, 7, 3, 3, 59829228055008383147496449202300549532701268377600000⟩,
  ⟨1, 5, 8, 7, 4, 3, 7962402076597398958712882641542285024886259712000000⟩
]

def collectedFourData_10_3_10 : List CollectedFourTerm := [
  ⟨1, 6, 3, 0, 6, 4, -3208677178447063475818341603580998767456896942080000⟩,
  ⟨1, 6, 4, 0, 7, 4, 46031469357557177333696345540067082359835962900480000⟩,
  ⟨1, 6, 5, 0, 8, 4, 2169636753635024012359364257116405271801469337600000⟩,
  ⟨1, 6, 3, 1, 5, 4, 43016899107342116163212742009355668870489220055040000⟩,
  ⟨1, 6, 4, 1, 6, 4, 103135087558376567183336495763877292138351736913920000⟩,
  ⟨1, 6, 5, 1, 7, 4, -17208553111154295258935341157075871776721233510400000⟩,
  ⟨1, 6, 6, 1, 8, 4, -3137626494278627341963770600800964419113294233600000⟩,
  ⟨1, 6, 3, 2, 4, 4, -56017247171809354020457171982866320046506356244480000⟩,
  ⟨1, 6, 4, 2, 5, 4, -13087302108555572236825956613011763100453814927360000⟩,
  ⟨1, 6, 5, 2, 6, 4, -12027883849597086277274291386323539628249002803200000⟩,
  ⟨1, 6, 6, 2, 7, 4, -4198503125595851097774890071583630536957388390400000⟩,
  ⟨1, 6, 7, 2, 8, 4, -4922542092889397956258274366102098549183768166400000⟩,
  ⟨1, 6, 3, 3, 3, 4, 74874993126236096052233431173833399701195708170240000⟩,
  ⟨1, 6, 4, 3, 4, 4, 8979196493903090756996940782218186199934550671360000⟩,
  ⟨1, 6, 5, 3, 5, 4, 4544853307021709971686843742344616244768931840000000⟩,
  ⟨1, 6, 6, 3, 6, 4, 11124805688794233614242718037319143408119945625600000⟩,
  ⟨1, 6, 7, 3, 7, 4, 2748644701379515323081713504088041098338474393600000⟩,
  ⟨1, 6, 8, 3, 8, 4, 2487604317938115037956005972522660693048033280000000⟩,
  ⟨1, 6, 3, 4, 2, 4, -102500469094444042201116123635664536754230132736000000⟩,
  ⟨1, 6, 4, 4, 3, 4, 20069811682519602708417740727679706294020944691200000⟩,
  ⟨1, 6, 5, 4, 4, 4, -16373324076521711354112022543178793404354632089600000⟩,
  ⟨1, 6, 6, 4, 5, 4, -8850909382929606797327294794993347866472638054400000⟩,
  ⟨1, 6, 7, 4, 6, 4, -902724572961635753387291133496108470163734528000000⟩,
  ⟨1, 6, 8, 4, 7, 4, 883662880371383719041211707812987526396940124160000⟩,
  ⟨1, 6, 3, 5, 1, 4, 85118676676611323670251427454557148720215380459520000⟩,
  ⟨1, 6, 4, 5, 2, 4, -137511555906136197677391643633510912041897657630720000⟩,
  ⟨1, 6, 5, 5, 3, 4, 42702570466799437729788040611694437690326070067200000⟩,
  ⟨1, 6, 6, 5, 4, 4, -9982773449557686915799326630938925884142885273600000⟩,
  ⟨1, 6, 7, 5, 5, 4, -2390813586270749566754538784465860643688703590400000⟩,
  ⟨1, 6, 8, 5, 6, 4, 1840018040260205815190589058377687496749471498240000⟩,
  ⟨1, 6, 3, 6, 0, 4, 46355674807469485313820534496676792642654510776320000⟩,
  ⟨1, 6, 4, 6, 1, 4, 73789541025582223370834884515283399087763415367680000⟩,
  ⟨1, 6, 5, 6, 2, 4, 631994823248131737776830843371052215260990668800000⟩,
  ⟨1, 6, 6, 6, 3, 4, 36964106593754923888502135422399932803495598489600000⟩,
  ⟨1, 6, 7, 6, 4, 4, 855876788597845601835733187682464853215988940800000⟩,
  ⟨1, 6, 8, 6, 5, 4, -1931016846153199524250822701990960274000136110080000⟩,
  ⟨1, 6, 4, 7, 0, 4, 1407995389298126466623597920441734233139209369026560000⟩,
  ⟨1, 6, 5, 7, 1, 4, -29461424066690166464911694569177642471983258009600000⟩,
  ⟨1, 6, 6, 7, 2, 4, -36479046058430725216974416061292791958669256294400000⟩,
  ⟨1, 6, 7, 7, 3, 4, 35860863997924660052304787384659123176379462451200000⟩,
  ⟨1, 6, 8, 7, 4, 4, 3818048499012841981730972540963408299389301555200000⟩
]

def collectedFourData_10_3_11 : List CollectedFourTerm := [
  ⟨1, 7, 2, 0, 5, 5, 6670995361985278601957511995033851257189040128000000⟩,
  ⟨1, 7, 3, 0, 6, 5, 1070764430400104603533830993639283472758682419200000⟩,
  ⟨1, 7, 4, 0, 7, 5, -7680557645094639430790238818322909838282693017600000⟩,
  ⟨1, 7, 5, 0, 8, 5, -241342432148888118115638668351352162440183808000000⟩,
  ⟨1, 7, 2, 1, 4, 5, -22991882605196031924658129995749099448144651878400000⟩,
  ⟨1, 7, 3, 1, 5, 5, -14355126087363063678906224543827239394921257369600000⟩,
  ⟨1, 7, 4, 1, 6, 5, -17208553111154295258935341157075871776721233510400000⟩,
  ⟨1, 7, 5, 1, 7, 5, 1914216310472741937023302184300092256296108032000000⟩,
  ⟨1, 7, 6, 1, 8, 5, 261763544531810780941637925263005419218927616000000⟩,
  ⟨1, 7, 2, 2, 3, 5, 8568933458273789704474972964602323215011597516800000⟩,
  ⟨1, 7, 3, 2, 4, 5, 18693459149896179014894860881990764913759564595200000⟩,
  ⟨1, 7, 4, 2, 5, 5, 2183675204515870495741949957824200569324254003200000⟩,
  ⟨1, 7, 5, 2, 6, 5, 1337937669521248871637766253039532152356601856000000⟩,
  ⟨1, 7, 6, 2, 7, 5, 350269562641658916285663280835659419378253824000000⟩,
  ⟨1, 7, 7, 2, 8, 5, 328539313061356861243537721750561330421773107200000⟩,
  ⟨1, 7, 2, 3, 2, 5, 4582058834896630497464691453965878587266433024000000⟩,
  ⟨1, 7, 3, 3, 3, 5, -24986458564469338417173533965019273085475985817600000⟩,
  ⟨1, 7, 4, 3, 4, 5, -1498219310410347712143565071404426904567231283200000⟩,
  ⟨1, 7, 5, 3, 5, 5, -505552806956666928026772611827882186191667200000000⟩,
  ⟨1, 7, 6, 3, 6, 5, -928111926208076543531860158528943462218203136000000⟩,
  ⟨1, 7, 7, 3, 7, 5, -183449491136988072620163932785607176107117772800000⟩,
  ⟨1, 7, 8, 3, 8, 5, -138355988694744858085571476583901625004851200000000⟩,
  ⟨1, 7, 2, 4, 1, 5, 10577395635436956473047928391708469627184165683200000⟩,
  ⟨1, 7, 3, 4, 2, 5, 34205328333707476379558496832048031767084400640000000⟩,
  ⟨1, 7, 4, 4, 3, 5, -3348738324132567226828847728302331454338105344000000⟩,
  ⟨1, 7, 5, 4, 4, 5, 1821308497087909857364605444625253546713939968000000⟩,
  ⟨1, 7, 6, 4, 5, 5, 738407014547530661252621829491708583072497664000000⟩,
  ⟨1, 7, 7, 4, 6, 5, 60249461657795161840605486309564046318239744000000⟩,
  ⟨1, 7, 8, 4, 7, 5, -49147708341319235424890991333915728833570406400000⟩,
  ⟨1, 7, 2, 5, 0, 5, -78918743765731702797385195514916111717409121894400000⟩,
  ⟨1, 7, 3, 5, 1, 5, -28404867887692382165317862097006626143946460364800000⟩,
  ⟨1, 7, 4, 5, 2, 5, 22944421430473807573366222021063212819280193126400000⟩,
  ⟨1, 7, 5, 5, 3, 5, -4750077264408437032952577494461035384171134976000000⟩,
  ⟨1, 7, 6, 5, 4, 5, 832835319047449760747412840195293858041430016000000⟩,
  ⟨1, 7, 7, 5, 5, 5, 159567198912482630230791615947349436681892659200000⟩,
  ⟨1, 7, 8, 5, 6, 5, -102338427916614041922871862858734588678216089600000⟩,
  ⟨1, 7, 3, 6, 0, 5, -15469305564436803732799529802202147110033083596800000⟩,
  ⟨1, 7, 4, 6, 1, 5, -12312116718451335663335573161210276100190083481600000⟩,
  ⟨1, 7, 5, 6, 2, 5, -70300785370023682552357517734303388248571904000000⟩,
  ⟨1, 7, 6, 6, 3, 5, -3083813698053804336960426082503353402419838976000000⟩,
  ⟨1, 7, 7, 6, 4, 5, -57122756268000943685205654069455132052317798400000⟩,
  ⟨1, 7, 8, 6, 5, 5, 107399614564578177963780755901284716572259123200000⟩,
  ⟨1, 7, 4, 7, 0, 5, -234930361825530513816113656979593250199376704307200000⟩,
  ⟨1, 7, 5, 7, 1, 5, 3277180720188372703724264763329946350222573568000000⟩,
  ⟨1, 7, 6, 7, 2, 5, 3043346432344999237664584672323830057023832064000000⟩,
  ⟨1, 7, 7, 7, 3, 5, -2393418563283299948485644640773701177649502617600000⟩,
  ⟨1, 7, 8, 7, 4, 5, -212352853368278237548630302149026696824619008000000⟩
]

def collectedFourData_10_3_12 : List CollectedFourTerm := [
  ⟨1, 8, 1, 0, 4, 6, -148162107323847065951276968648774306165161984000000⟩,
  ⟨1, 8, 2, 0, 5, 6, 3648957292767572064238941888907412916305657856000000⟩,
  ⟨1, 8, 3, 0, 6, 6, 292847878399799080474239116990983199364690739200000⟩,
  ⟨1, 8, 4, 0, 7, 6, -1400392060995692697154290285220228491156809318400000⟩,
  ⟨1, 8, 5, 0, 8, 6, -33002879632563130510600367410677015908450304000000⟩,
  ⟨1, 8, 1, 1, 3, 6, 598380889539468812518549160720901295774787174400000⟩,
  ⟨1, 8, 2, 1, 4, 6, -12576293814378923143388113953205544649466105036800000⟩,
  ⟨1, 8, 3, 1, 5, 6, -3926043954668025126523143739460260977662597529600000⟩,
  ⟨1, 8, 4, 1, 6, 6, -3137626494278627341963770600800964419113294233600000⟩,
  ⟨1, 8, 5, 1, 7, 6, 261763544531810780941637925263005419218927616000000⟩,
  ⟨1, 8, 6, 1, 8, 6, 28636326154356210840937846308808439739344486400000⟩,
  ⟨1, 8, 1, 2, 2, 6, 104464311768392742591045162983638359730657689600000⟩,
  ⟨1, 8, 2, 2, 3, 6, 4687107476042822856985007318273163772007389593600000⟩,
  ⟨1, 8, 3, 2, 4, 6, 5112552954299062540773596339995101557869982515200000⟩,
  ⟨1, 8, 4, 2, 5, 6, 398148358687240880187732222864605868918099148800000⟩,
  ⟨1, 8, 5, 2, 6, 6, 182959106983066152118411817897604312861769728000000⟩,
  ⟨1, 8, 6, 2, 7, 6, 38318679767614856857126579178021374519777689600000⟩,
  ⟨1, 8, 7, 2, 8, 6, 29951200615618418869360582771658271136048742400000⟩,
  ⟨1, 8, 1, 3, 1, 6, -586255824410148831562882352638252684243107840000000⟩,
  ⟨1, 8, 2, 3, 2, 6, 2506333177319190138368090586555507241383886848000000⟩,
  ⟨1, 8, 3, 3, 3, 6, -6833651895398840926774996117478413202995386777600000⟩,
  ⟨1, 8, 4, 3, 4, 6, -273169543785546276425745224870753717671742668800000⟩,
  ⟨1, 8, 5, 3, 5, 6, -69132884289498823125019553086785740970393600000000⟩,
  ⟨1, 8, 6, 3, 6, 6, -101533297442846975263424348387442517097211494400000⟩,
  ⟨1, 8, 7, 3, 7, 6, -16724124917284717840853946292710521750264217600000⟩,
  ⟨1, 8, 8, 3, 8, 6, -10811303615792327058997160318655291142963200000000⟩,
  ⟨1, 8, 1, 4, 0, 6, 4690927974995016723323773548169308780331479859200000⟩,
  ⟨1, 8, 2, 4, 1, 6, 5785713053011225150900075777029060010365576806400000⟩,
  ⟨1, 8, 3, 4, 2, 6, 9354959455229388598307189775317395892223344640000000⟩,
  ⟨1, 8, 4, 4, 3, 6, -610573708337747067019671004728745897802858496000000⟩,
  ⟨1, 8, 5, 4, 4, 6, 249058669741402412364911031962523038996496384000000⟩,
  ⟨1, 8, 6, 4, 5, 6, 80780019009399774709202815056875116356540825600000⟩,
  ⟨1, 8, 7, 4, 6, 6, 5492626426593344880170516302031898487554048000000⟩,
  ⟨1, 8, 8, 4, 7, 6, -3840461131543296407290207031871513024685670400000⟩,
  ⟨1, 8, 2, 5, 0, 6, -43167639905886888204242116413862500805963992268800000⟩,
  ⟨1, 8, 3, 5, 1, 6, -7768567073178791573726318176406281046494858444800000⟩,
  ⟨1, 8, 4, 5, 2, 6, 4183444366945967531870883084392143706870356377600000⟩,
  ⟨1, 8, 5, 5, 3, 6, -649559328655206111750590826625706379379212288000000⟩,
  ⟨1, 8, 6, 5, 4, 6, 91110257051901268442055571492327914016761446400000⟩,
  ⟨1, 8, 7, 5, 5, 6, 14546901987974584355706303397524573463668326400000⟩,
  ⟨1, 8, 8, 5, 6, 6, -7996848030991060287114598481901841039333785600000⟩,
  ⟨1, 8, 3, 6, 0, 6, -4230765597219899793056672839617180032373148876800000⟩,
  ⟨1, 8, 4, 6, 1, 6, -2244861806041316186082307852965346144592225894400000⟩,
  ⟨1, 8, 5, 6, 2, 6, -9613429089047305729145341793994262972465152000000⟩,
  ⟨1, 8, 6, 6, 3, 6, -337362083840549280754836633303390602658211430400000⟩,
  ⟨1, 8, 7, 6, 4, 6, -5207581146857910200319635439131481397316812800000⟩,
  ⟨1, 8, 8, 6, 5, 6, 8392335252206030745231637546650430461915955200000⟩,
  ⟨1, 8, 4, 7, 0, 6, -42834730079454358157158076629984386572484398284800000⟩,
  ⟨1, 8, 5, 7, 1, 6, 448144985858972174324297007081274674128093184000000⟩,
  ⟨1, 8, 6, 7, 2, 6, 332935058597270950370042998368700107656370585600000⟩,
  ⟨1, 8, 7, 7, 3, 6, -218195377831862519042018334340963112288727859200000⟩,
  ⟨1, 8, 8, 7, 4, 6, -16593507755631293362498962325325892538073088000000⟩
]

def collectedFourData_10_3_13 : List CollectedFourTerm := [
  ⟨2, 1, 7, 2, 8, 0, -13575799666729021791439933448034483938166571008000000⟩,
  ⟨2, 1, 7, 3, 7, 0, 7580443014361630210730686989804950473452552192000000⟩,
  ⟨2, 1, 8, 3, 8, 0, 34302619696437327819955230726096229402411008000000000⟩,
  ⟨2, 1, 7, 4, 6, 0, -2489609580883685311895392364986669583208284160000000⟩,
  ⟨2, 1, 8, 4, 7, 0, 12185198227329998486681287515867601262792933376000000⟩,
  ⟨2, 1, 7, 5, 5, 0, -6593586337146822541564786458486382053229068288000000⟩,
  ⟨2, 1, 8, 5, 6, 0, 25372780797367928357162235300478567070526603264000000⟩,
  ⟨2, 1, 7, 6, 4, 0, 2360408829858797065251417910997931057035083776000000⟩,
  ⟨2, 1, 8, 6, 5, 0, -26627601513374957620807165502812411238692159488000000⟩,
  ⟨2, 1, 7, 7, 3, 0, 98900100054985741924449258215397738650705854464000000⟩,
  ⟨2, 1, 8, 7, 4, 0, 52648672740987359011434158333796025979602206720000000⟩
]

def collectedFourData_10_3_14 : List CollectedFourTerm := [
  ⟨2, 2, 6, 1, 8, 1, 104464311768392742591045162983638359730657689600000⟩,
  ⟨2, 2, 6, 2, 7, 1, 139785197592058706905591011158581294131471974400000⟩,
  ⟨2, 2, 7, 2, 8, 1, 655565565655846292353573699104553123836434841600000⟩,
  ⟨2, 2, 6, 3, 6, 1, -370389902034588453279375256794355477440469401600000⟩,
  ⟨2, 2, 7, 3, 7, 1, -366054120908315209503239963700906808593245798400000⟩,
  ⟨2, 2, 8, 3, 8, 1, -828224371190596648853903983075706075401420800000000⟩,
  ⟨2, 2, 6, 4, 5, 1, 294682671407237429230104672455708167161407078400000⟩,
  ⟨2, 2, 7, 4, 6, 1, 120221449433591215853893526368210434373189632000000⟩,
  ⟨2, 2, 8, 4, 7, 1, -294207213005114148956792826295610130256468377600000⟩,
  ⟨2, 2, 6, 5, 4, 1, 332367016867502633191741336745158221034527129600000⟩,
  ⟨2, 2, 7, 5, 5, 1, 318399524368776595667954304575450848719116697600000⟩,
  ⟨2, 2, 8, 5, 6, 1, -612616634158686432652156444182521933994550886400000⟩,
  ⟨2, 2, 6, 6, 3, 1, -1230685029748226549504507892007994512308279705600000⟩,
  ⟨2, 2, 7, 6, 4, 1, -113982438435486328893687351902761550605398835200000⟩,
  ⟨2, 2, 8, 6, 5, 1, 642913827424651336039007813414719586837515468800000⟩,
  ⟨2, 2, 6, 7, 2, 1, 1214535397189651257937246961531671670096815718400000⟩,
  ⟨2, 2, 7, 7, 3, 1, -4775814436541999139278775644581655077981048012800000⟩,
  ⟨2, 2, 8, 7, 4, 1, -1271183200024007815056181546178527380973289472000000⟩
]

def collectedFourData_10_3_15 : List CollectedFourTerm := [
  ⟨2, 3, 5, 0, 8, 2, -1080362355303015213292202569289664457405051699200000⟩,
  ⟨2, 3, 5, 1, 7, 2, 8568933458273789704474972964602323215011597516800000⟩,
  ⟨2, 3, 6, 1, 8, 2, 4687107476042822856985007318273163772007389593600000⟩,
  ⟨2, 3, 5, 2, 6, 2, 5989238937481483187584677230341441047121782374400000⟩,
  ⟨2, 3, 6, 2, 7, 2, 6271885906131041751311991745702308095984035430400000⟩,
  ⟨2, 3, 7, 2, 8, 2, 14706966483607528734823875563189982174487825612800000⟩,
  ⟨2, 3, 5, 3, 5, 2, -2263092388647213474987094402114861430766305280000000⟩,
  ⟨2, 3, 6, 3, 6, 2, -16618663823929567963978891547956456444307020185600000⟩,
  ⟨2, 3, 7, 3, 7, 2, -8212062941407178191886401766045260570707571507200000⟩,
  ⟨2, 3, 8, 3, 8, 2, -12386930925127874628902857371613666075056537600000000⟩,
  ⟨2, 3, 5, 4, 4, 2, 8153034342644724728876465856433924146979877683200000⟩,
  ⟨2, 3, 6, 4, 5, 2, 13221829817587894427759696643123086525217531494400000⟩,
  ⟨2, 3, 7, 4, 6, 2, 2697049570719434248669504174511488415255494656000000⟩,
  ⟨2, 3, 8, 4, 7, 2, -4400165645850181637012475369923791831671452467200000⟩,
  ⟨2, 3, 5, 5, 3, 2, -21263582270032431104518061161144573891898140262400000⟩,
  ⟨2, 3, 6, 5, 4, 2, 14912652016543228973338226748378061483816884633600000⟩,
  ⟨2, 3, 7, 5, 5, 2, 7142979098671053026083289989285394524301741260800000⟩,
  ⟨2, 3, 8, 5, 6, 2, -9162299728030677366763943018378474245461953740800000⟩,
  ⟨2, 3, 5, 6, 2, 2, -314699414378800724037583489025781402204477849600000⟩,
  ⟨2, 3, 6, 6, 3, 2, -55218408142829491620026164476919418893505239449600000⟩,
  ⟨2, 3, 7, 6, 4, 2, -2557083516297110968690258118632805867267398041600000⟩,
  ⟨2, 3, 8, 6, 5, 2, 9615424814981774258584815253009430738133162393600000⟩,
  ⟨2, 3, 5, 7, 1, 2, 14670203867971807570345325706424737646649750323200000⟩,
  ⟨2, 3, 6, 7, 2, 2, 54493806006279107370347592539063952281440773734400000⟩,
  ⟨2, 3, 7, 7, 3, 2, -107140683601775721952573612370506909228269463142400000⟩,
  ⟨2, 3, 8, 7, 4, 2, -19011827035764448309291489954598017167035203584000000⟩
]

def collectedFourData_10_3_16 : List CollectedFourTerm := [
  ⟨2, 4, 4, 0, 7, 3, -25001735662699013394886274677938411189436541829120000⟩,
  ⟨2, 4, 5, 0, 8, 3, -2356852186364271171110358116432408321110887628800000⟩,
  ⟨2, 4, 4, 1, 6, 3, -56017247171809354020457171982866320046506356244480000⟩,
  ⟨2, 4, 5, 1, 7, 3, 18693459149896179014894860881990764913759564595200000⟩,
  ⟨2, 4, 6, 1, 8, 3, 5112552954299062540773596339995101557869982515200000⟩,
  ⟨2, 4, 4, 2, 5, 3, 7108295095130853097673810608032462271971946659840000⟩,
  ⟨2, 4, 5, 2, 6, 3, 13065755961574702626024863293831232317975796121600000⟩,
  ⟨2, 4, 6, 2, 7, 3, 6841180617750347368414939357481243338125135052800000⟩,
  ⟨2, 4, 7, 2, 8, 3, 10694605052812605352127536432231699255044499046400000⟩,
  ⟨2, 4, 4, 3, 4, 3, -4877000459407287876365122039375420274998341795840000⟩,
  ⟨2, 4, 5, 3, 5, 3, -4937023414363167784704599840670843001550929920000000⟩,
  ⟨2, 4, 6, 3, 6, 3, -18127128354493446862996006654179554102575575859200000⟩,
  ⟨2, 4, 7, 3, 7, 3, -5971644113358003413707880304838971098549295513600000⟩,
  ⟨2, 4, 8, 3, 8, 3, -6755642005186904691508153492381181717092761600000000⟩,
  ⟨2, 4, 4, 4, 3, 3, -10900806198230218230645375261806671568225225932800000⟩,
  ⟨2, 4, 5, 4, 4, 3, 17786159173026471337253543076169669412960128204800000⟩,
  ⟨2, 4, 6, 4, 5, 3, 14421966093301256964552447521748140828436253900800000⟩,
  ⟨2, 4, 7, 4, 6, 3, 1961239253441672544280336951768072789193392128000000⟩,
  ⟨2, 4, 8, 4, 7, 3, -2399782807102315480991339954655052682132402995200000⟩,
  ⟨2, 4, 4, 5, 2, 3, 74688634086959452338734783953110055079911285063680000⟩,
  ⟨2, 4, 5, 5, 3, 3, -46387325620029052371299989992103019006691744153600000⟩,
  ⟨2, 4, 6, 5, 4, 3, 16266263044597484263456506179178449839540351795200000⟩,
  ⟨2, 4, 7, 5, 5, 3, 5194228221430198408977601185192740317131335270400000⟩,
  ⟨2, 4, 8, 5, 6, 3, -4996977643690025670330712697494398813206269132800000⟩,
  ⟨2, 4, 4, 6, 1, 3, -40078377361000135030001289268087942029762279505920000⟩,
  ⟨2, 4, 5, 6, 2, 3, -686528921695169150068306006749001079413171814400000⟩,
  ⟨2, 4, 6, 6, 3, 3, -60230544557654833844742304331128884536664077107200000⟩,
  ⟨2, 4, 7, 6, 4, 3, -1859458803032972982391466098629253157293444300800000⟩,
  ⟨2, 4, 8, 6, 5, 3, 5244105111301959367667338999084793360167836057600000⟩,
  ⟨2, 4, 4, 7, 0, 3, -764744837148055038527032846473574272778430463344640000⟩,
  ⟨2, 4, 5, 7, 1, 3, 32003616093177700407154151429631879429493673164800000⟩,
  ⟨2, 4, 6, 7, 2, 3, 59440170790283975788759641149351626222569573580800000⟩,
  ⟨2, 4, 7, 7, 3, 3, -77910512510278249608457879954637130559862813491200000⟩,
  ⟨2, 4, 8, 7, 4, 3, -10368758661406069218474806223312652029860511744000000⟩
]

def collectedFourData_10_3_17 : List CollectedFourTerm := [
  ⟨2, 5, 3, 0, 6, 4, 407164318151138842807129738632462796568804720640000⟩,
  ⟨2, 5, 4, 0, 7, 4, -5841152223214847651712911324067732340583788707840000⟩,
  ⟨2, 5, 5, 0, 8, 4, -275315533567325868822179555458572315599359180800000⟩,
  ⟨2, 5, 3, 1, 5, 4, -5458619056995373644196949059497214636812738232320000⟩,
  ⟨2, 5, 4, 1, 6, 4, -13087302108555572236825956613011763100453814927360000⟩,
  ⟨2, 5, 5, 1, 7, 4, 2183675204515870495741949957824200569324254003200000⟩,
  ⟨2, 5, 6, 1, 8, 4, 398148358687240880187732222864605868918099148800000⟩,
  ⟨2, 5, 3, 2, 4, 4, 7108295095130853097673810608032462271971946659840000⟩,
  ⟨2, 5, 4, 2, 5, 4, 1660710050628081109972331819389446286633473146880000⟩,
  ⟨2, 5, 5, 2, 6, 4, 1526275425685703137586577400378223508078565785600000⟩,
  ⟨2, 5, 6, 2, 7, 4, 532768043439014613914194013062022605416117043200000⟩,
  ⟨2, 5, 7, 2, 8, 4, 624644793899654747744328237006212144573920051200000⟩,
  ⟨2, 5, 3, 3, 3, 4, -9501244228492302538199593280267849332686764113920000⟩,
  ⟨2, 5, 4, 3, 4, 4, -1139412977579310269723238657842409966563890298880000⟩,
  ⟨2, 5, 5, 3, 5, 4, -576718066336000049321161697387498189849886720000000⟩,
  ⟨2, 5, 6, 3, 6, 4, -1411679539863858584872937935840654749571271884800000⟩,
  ⟨2, 5, 7, 3, 7, 4, -348788607714839534990680188926351440838708428800000⟩,
  ⟨2, 5, 8, 3, 8, 4, -315663951096915113360197735345926074259210240000000⟩,
  ⟨2, 5, 3, 4, 2, 4, 13006772351343203732392896646597637345208434688000000⟩,
  ⟨2, 5, 4, 4, 3, 4, -2546753922153615296155199284169921092617083289600000⟩,
  ⟨2, 5, 5, 4, 4, 4, 2077689017226440595143796987574227197741550796800000⟩,
  ⟨2, 5, 6, 4, 5, 4, 1123134015514208328620800426684730778022261555200000⟩,
  ⟨2, 5, 7, 4, 6, 4, 114551017377850665485633781406810693775130624000000⟩,
  ⟨2, 5, 8, 4, 7, 4, -112132188485231161486242780152257457826331361280000⟩,
  ⟨2, 5, 3, 5, 1, 4, -10801113986709357548789860969080095219017486172160000⟩,
  ⟨2, 5, 4, 5, 2, 4, 17449495784278963740020234633540131248364333301760000⟩,
  ⟨2, 5, 5, 5, 3, 4, -5418732399820383068178332289997047415887731097600000⟩,
  ⟨2, 5, 6, 5, 4, 4, 1266761633781323003154804871347271216145419468800000⟩,
  ⟨2, 5, 7, 5, 5, 4, 303381714501906126533986356911037536747598643200000⟩,
  ⟨2, 5, 8, 5, 6, 4, -233488646280999351708661521702402391512365137920000⟩,
  ⟨2, 5, 3, 6, 0, 4, -5882292195737205242387873824383927656743761346560000⟩,
  ⟨2, 5, 4, 6, 1, 4, -9363506045474977606191978018783814453934099005440000⟩,
  ⟨2, 5, 5, 6, 2, 4, -80196830959297581301772742266719808950527590400000⟩,
  ⟨2, 5, 6, 6, 3, 4, -4690551408040483380843306054473034036084001996800000⟩,
  ⟨2, 5, 7, 6, 4, 4, -108606279058427082296949435285972999194699366400000⟩,
  ⟨2, 5, 8, 6, 5, 4, 245035917849129118667670862822133018579844464640000⟩,
  ⟨2, 5, 4, 7, 0, 4, -178667235985696084176847912678336546835251310100480000⟩,
  ⟨2, 5, 5, 7, 1, 4, 3738500314849718653054612595251920040987774156800000⟩,
  ⟨2, 5, 6, 7, 2, 4, 4628999768176578611633294839131944653564359475200000⟩,
  ⟨2, 5, 7, 7, 3, 4, -4550555704420362185206269872163823224408873369600000⟩,
  ⟨2, 5, 8, 7, 4, 4, -484490345183595460140538063208829143410645401600000⟩
]

def collectedFourData_10_3_18 : List CollectedFourTerm := [
  ⟨2, 6, 2, 0, 5, 5, 4662678893273769994379737596261845026077671424000000⟩,
  ⟨2, 6, 3, 0, 6, 5, 748408661433858162797115735568779819397781913600000⟩,
  ⟨2, 6, 4, 0, 7, 5, -5368310436015304715702216455595588736999279820800000⟩,
  ⟨2, 6, 5, 0, 8, 5, -168685811242580334598753792033931223172644864000000⟩,
  ⟨2, 6, 2, 1, 4, 5, -16070130456210089708214417331465546828252132147200000⟩,
  ⟨2, 6, 3, 1, 5, 5, -10033486726621282994015279745080199749489708236800000⟩,
  ⟨2, 6, 4, 1, 6, 5, -12027883849597086277274291386323539628249002803200000⟩,
  ⟨2, 6, 5, 1, 7, 5, 1337937669521248871637766253039532152356601856000000⟩,
  ⟨2, 6, 6, 1, 8, 5, 182959106983066152118411817897604312861769728000000⟩,
  ⟨2, 6, 2, 2, 3, 5, 5989238937481483187584677230341441047121782374400000⟩,
  ⟨2, 6, 3, 2, 4, 5, 13065755961574702626024863293831232317975796121600000⟩,
  ⟨2, 6, 4, 2, 5, 5, 1526275425685703137586577400378223508078565785600000⟩,
  ⟨2, 6, 5, 2, 6, 5, 935148863652648783793527325916836411786395648000000⟩,
  ⟨2, 6, 6, 2, 7, 5, 244820211687189858887404446266888088339873792000000⟩,
  ⟨2, 6, 7, 2, 8, 5, 229631897115570586318149137725769006341265817600000⟩,
  ⟨2, 6, 2, 3, 2, 5, 3202620877081981118537718191771984520535867392000000⟩,
  ⟨2, 6, 3, 3, 3, 5, -17464235341866499796281628109942988942984662220800000⟩,
  ⟨2, 6, 4, 3, 4, 5, -1047177396637639403244168363187904109352688025600000⟩,
  ⟨2, 6, 5, 3, 5, 5, -353355125363278812231858383238442912422297600000000⟩,
  ⟨2, 6, 6, 3, 6, 5, -648701978356376351279268996016718972492709888000000⟩,
  ⟨2, 6, 7, 3, 7, 5, -128221655673838171375896983342841702008645222400000⟩,
  ⟨2, 6, 8, 3, 8, 5, -96703642146293970226782442560489678018969600000000⟩,
  ⟨2, 6, 2, 4, 1, 5, 7393049567415788191060041576429762100546083225600000⟩,
  ⟨2, 6, 3, 4, 2, 5, 23907745966654902096694554526412063798061957120000000⟩,
  ⟨2, 6, 4, 4, 3, 5, -2340593967731850842511532142559718731732221952000000⟩,
  ⟨2, 6, 5, 4, 4, 5, 1272999938795446761583160348458995099730182144000000⟩,
  ⟨2, 6, 6, 4, 5, 5, 516108108993115902667151708065661657926336512000000⟩,
  ⟨2, 6, 7, 4, 6, 5, 42111240970688703823377004765862259591217152000000⟩,
  ⟨2, 6, 8, 4, 7, 5, -34351692648703435205271221131698983645950771200000⟩,
  ⟨2, 6, 2, 5, 0, 5, -55160098437041930165963716223779713435550561075200000⟩,
  ⟨2, 6, 3, 5, 1, 5, -19853525715352676477500216674356886459675731558400000⟩,
  ⟨2, 6, 4, 5, 2, 5, 16036957562868212667694378895853681213168628531200000⟩,
  ⟨2, 6, 5, 5, 3, 5, -3320057023032555361504951636869666269307076608000000⟩,
  ⟨2, 6, 6, 5, 4, 5, 582108583948980961335885131442826354442108928000000⟩,
  ⟨2, 6, 7, 5, 5, 5, 111529175191426537036923815434156856011495833600000⟩,
  ⟨2, 6, 8, 5, 6, 5, -71529239929738158098488073635890233539873996800000⟩,
  ⟨2, 6, 3, 6, 0, 5, -10812240248273333934776033167663879953091815014400000⟩,
  ⟨2, 6, 4, 6, 1, 5, -8605529405968853976495633676227522272923798732800000⟩,
  ⟨2, 6, 5, 6, 2, 5, -49136593617392208361686145358855938278162432000000⟩,
  ⟨2, 6, 6, 6, 3, 5, -2155425429110909220682265631639027995123908608000000⟩,
  ⟨2, 6, 7, 6, 4, 5, -39925836479245585813154405944071984268915507200000⟩,
  ⟨2, 6, 8, 6, 5, 5, 75066746235447605332473211676244720196622745600000⟩,
  ⟨2, 6, 4, 7, 0, 5, -164204107488253455805803827325882945429304875417600000⟩,
  ⟨2, 6, 5, 7, 1, 5, 2290578923280591341100256964406794294283730944000000⟩,
  ⟨2, 6, 6, 7, 2, 5, 2127140914514455611059599432957177837714931712000000⟩,
  ⟨2, 6, 7, 7, 3, 5, -1672875127658543363328464954040604786175036620800000⟩,
  ⟨2, 6, 8, 7, 4, 5, -148423603015677787902093786766659506839486464000000⟩
]

def collectedFourData_10_3_19 : List CollectedFourTerm := [
  ⟨2, 7, 1, 0, 4, 6, -198257846122968067666810047619553801143320576000000⟩,
  ⟨2, 7, 2, 0, 5, 6, 4882722219099787632512236702580313038398685184000000⟩,
  ⟨2, 7, 3, 0, 6, 6, 391863956728970097705322428928762746795510988800000⟩,
  ⟨2, 7, 4, 0, 7, 6, -1873884752015966378374430740985635562919139737600000⟩,
  ⟨2, 7, 5, 0, 8, 6, -44161627760233758501564461231489622585901056000000⟩,
  ⟨2, 7, 1, 1, 3, 6, 800702071967265852677253833223395095034304921600000⟩,
  ⟨2, 7, 2, 1, 4, 6, -16828519578211080578549204818231542068527969075200000⟩,
  ⟨2, 7, 3, 1, 5, 6, -5253495865412153752227305664414668056433157734400000⟩,
  ⟨2, 7, 4, 1, 6, 6, -4198503125595851097774890071583630536957388390400000⟩,
  ⟨2, 7, 5, 1, 7, 6, 350269562641658916285663280835659419378253824000000⟩,
  ⟨2, 7, 6, 1, 8, 6, 38318679767614856857126579178021374519777689600000⟩,
  ⟨2, 7, 1, 2, 2, 6, 139785197592058706905591011158581294131471974400000⟩,
  ⟨2, 7, 2, 2, 3, 6, 6271885906131041751311991745702308095984035430400000⟩,
  ⟨2, 7, 3, 2, 4, 6, 6841180617750347368414939357481243338125135052800000⟩,
  ⟨2, 7, 4, 2, 5, 6, 532768043439014613914194013062022605416117043200000⟩,
  ⟨2, 7, 5, 2, 6, 6, 244820211687189858887404446266888088339873792000000⟩,
  ⟨2, 7, 6, 2, 7, 6, 51274776352889542840180705791679305083151974400000⟩,
  ⟨2, 7, 7, 2, 8, 6, 40078132189833379114160318066588533499992473600000⟩,
  ⟨2, 7, 1, 3, 1, 6, -784477347980414360079979548489061075003637760000000⟩,
  ⟨2, 7, 2, 3, 2, 6, 3353760461274569710015571988057668604471017472000000⟩,
  ⟨2, 7, 3, 3, 3, 6, -9144207857239689475448652307821775304970888806400000⟩,
  ⟨2, 7, 4, 3, 4, 6, -365532094241476502565488507142156382511510323200000⟩,
  ⟨2, 7, 5, 3, 5, 6, -92507706478189223947596051406086157526630400000000⟩,
  ⟨2, 7, 6, 3, 6, 6, -135863165180167256930797359903003409835989401600000⟩,
  ⟨2, 7, 7, 3, 7, 6, -22378792015592917550495521452614718939620966400000⟩,
  ⟨2, 7, 8, 3, 8, 6, -14466760815998826316349224261782355102924800000000⟩,
  ⟨2, 7, 1, 4, 0, 6, 6276998170711090011585414997420676174534462668800000⟩,
  ⟨2, 7, 2, 4, 1, 6, 7741945824706318642978153194305564264208374169600000⟩,
  ⟨2, 7, 3, 4, 2, 6, 12518005755058234096059703202130205481065512960000000⟩,
  ⟨2, 7, 4, 4, 3, 6, -817017458112730108797729643292436355973382144000000⟩,
  ⟨2, 7, 5, 4, 4, 6, 333268987010652454021077484060007646338482176000000⟩,
  ⟨2, 7, 6, 4, 5, 6, 108092904912390627816718495164584196621887078400000⟩,
  ⟨2, 7, 7, 4, 6, 6, 7349762395821573627092989463219526300598272000000⟩,
  ⟨2, 7, 8, 4, 7, 6, -5138976259257087253696983086424884034247065600000⟩,
  ⟨2, 7, 2, 5, 0, 6, -57763239633508740293677910190834451630819324723200000⟩,
  ⟨2, 7, 3, 5, 1, 6, -10395231299078192210963753969613721431071470387200000⟩,
  ⟨2, 7, 4, 5, 2, 6, 5597927058050672417142601264018597796460783206400000⟩,
  ⟨2, 7, 5, 5, 3, 6, -869184677204809110866676046043572157527621632000000⟩,
  ⟨2, 7, 6, 5, 4, 6, 121915944967884311133356668151726049391647129600000⟩,
  ⟨2, 7, 7, 5, 5, 6, 19465418709211152677629085335490468647639449600000⟩,
  ⟨2, 7, 8, 5, 6, 6, -10700697331009178840144358026737997828220518400000⟩,
  ⟨2, 7, 3, 6, 0, 6, -5661248276677054461199200106100629196237910835200000⟩,
  ⟨2, 7, 4, 6, 1, 6, -3003881859864945938869591308146832302178671001600000⟩,
  ⟨2, 7, 5, 6, 2, 6, -12863867688412935549154274009999037356310528000000⟩,
  ⟨2, 7, 6, 6, 3, 6, -451429055065945413728221391417070252652599705600000⟩,
  ⟨2, 7, 7, 6, 4, 6, -6968339208553162165686818590692710284473139200000⟩,
  ⟨2, 7, 8, 6, 5, 6, 11229904468134028628635020073160913927851212800000⟩,
  ⟨2, 7, 4, 7, 0, 6, -57317768208096168809095369426987536156099556147200000⟩,
  ⟨2, 7, 5, 7, 1, 6, 599669249121887009421314935629499857031397376000000⟩,
  ⟨2, 7, 6, 7, 2, 6, 445505188935005848764753762417748843365295718400000⟩,
  ⟨2, 7, 7, 7, 3, 6, -291970372346139278042388623035644646217534668800000⟩,
  ⟨2, 7, 8, 7, 4, 6, -22204011313537288319808636964409388231032832000000⟩
]

def collectedFourData_10_3_20 : List CollectedFourTerm := [
  ⟨2, 8, 0, 0, 3, 7, 33594811991758933568905936798481115232605516595200000⟩,
  ⟨2, 8, 1, 0, 4, 7, -929790988446526592902270314628075515820376064000000⟩,
  ⟨2, 8, 2, 0, 5, 7, 11449511853343651865709169655076996485153292288000000⟩,
  ⟨2, 8, 3, 0, 6, 7, 612588745395074166800397765302449152652109414400000⟩,
  ⟨2, 8, 4, 0, 7, 7, -2197039347854027693509940321225759618825296281600000⟩,
  ⟨2, 8, 5, 0, 8, 7, -41421900146264536242918715587732181086948556800000⟩,
  ⟨2, 8, 0, 1, 2, 7, -13140689032699289464156826665601664014690864332800000⟩,
  ⟨2, 8, 1, 1, 3, 7, 3755137995819161304600665644640666943878489702400000⟩,
  ⟨2, 8, 2, 1, 4, 7, -39461252501985867078274599242519954171831412326400000⟩,
  ⟨2, 8, 3, 1, 5, 7, -8212626820784408404932362965705803718812971827200000⟩,
  ⟨2, 8, 4, 1, 6, 7, -4922542092889397956258274366102098549183768166400000⟩,
  ⟨2, 8, 5, 1, 7, 7, 328539313061356861243537721750561330421773107200000⟩,
  ⟨2, 8, 6, 1, 8, 7, 29951200615618418869360582771658271136048742400000⟩,
  ⟨2, 8, 0, 2, 1, 7, -13575799666729021791439933448034483938166571008000000⟩,
  ⟨2, 8, 1, 2, 2, 7, 655565565655846292353573699104553123836434841600000⟩,
  ⟨2, 8, 2, 2, 3, 7, 14706966483607528734823875563189982174487825612800000⟩,
  ⟨2, 8, 3, 2, 4, 7, 10694605052812605352127536432231699255044499046400000⟩,
  ⟨2, 8, 4, 2, 5, 7, 624644793899654747744328237006212144573920051200000⟩,
  ⟨2, 8, 5, 2, 6, 7, 229631897115570586318149137725769006341265817600000⟩,
  ⟨2, 8, 6, 2, 7, 7, 40078132189833379114160318066588533499992473600000⟩,
  ⟨2, 8, 7, 2, 8, 7, 26851242224346870664202068440629321512727347200000⟩,
  ⟨2, 8, 0, 3, 0, 7, 75858228979172544352508066054612146845339824947200000⟩,
  ⟨2, 8, 1, 3, 1, 7, -3679047175465701104655411024886193948605808640000000⟩,
  ⟨2, 8, 2, 3, 2, 7, 7864244253837145247268539201033068487381090304000000⟩,
  ⟨2, 8, 3, 3, 3, 7, -14294855963934887370683036914059123079483962163200000⟩,
  ⟨2, 8, 4, 3, 4, 7, -428568722322987255131459575244929180883956531200000⟩,
  ⟨2, 8, 5, 3, 5, 7, -86768653576441904502854497877752494025605120000000⟩,
  ⟨2, 8, 6, 3, 6, 7, -106195331918069982720508054981774502412052070400000⟩,
  ⟨2, 8, 7, 3, 7, 7, -14993172891709635741047961848479215279459532800000⟩,
  ⟨2, 8, 8, 3, 8, 7, -8480789097234579536139313888978679522918400000000⟩,
  ⟨2, 8, 1, 4, 0, 7, 29437908500239536178676746245867992716225491763200000⟩,
  ⟨2, 8, 2, 4, 1, 7, 18154114960949375588745686148890191516241441587200000⟩,
  ⟨2, 8, 3, 4, 2, 7, 19569009368328377334293363297642165677043220480000000⟩,
  ⟨2, 8, 4, 4, 3, 7, -957913501044408699325347505837894437389205504000000⟩,
  ⟨2, 8, 5, 4, 4, 7, 312593430132406590047517883497318451178687692800000⟩,
  ⟨2, 8, 6, 4, 5, 7, 84489139495149576149927167037420436434033049600000⟩,
  ⟨2, 8, 7, 4, 6, 7, 4924137917576480754945917654818021435244544000000⟩,
  ⟨2, 8, 8, 4, 7, 7, -3012600704800260064550725107746210635893964800000⟩,
  ⟨2, 8, 2, 5, 0, 7, -135449216071382656397563006125559205418796213862400000⟩,
  ⟨2, 8, 3, 5, 1, 7, -16250542031856988538227682110918247378901899673600000⟩,
  ⟨2, 8, 4, 5, 2, 7, 6563299050127108904547467364847832059024402022400000⟩,
  ⟨2, 8, 5, 5, 3, 7, -815261636262888555531472371125450366726543769600000⟩,
  ⟨2, 8, 6, 5, 4, 7, 95293703961635392749686428611657519356864102400000⟩,
  ⟨2, 8, 7, 5, 5, 7, 13041293199086457103958841041560361667605299200000⟩,
  ⟨2, 8, 8, 5, 6, 7, -6273025344918177230060519243740279280448307200000⟩,
  ⟨2, 8, 3, 6, 0, 7, -8850053493381764738967747965499417465902963097600000⟩,
  ⟨2, 8, 4, 6, 1, 7, -3521906368749828292747846213759007665092663705600000⟩,
  ⟨2, 8, 5, 6, 2, 7, -12065810748126711054883810345795909056882278400000⟩,
  ⟨2, 8, 6, 6, 3, 7, -352852506244914113927972889598836225937401446400000⟩,
  ⟨2, 8, 7, 6, 4, 7, -4668594911160514532985014706341676893759078400000⟩,
  ⟨2, 8, 8, 6, 5, 7, 6583260246551703711692692763516409838200422400000⟩,
  ⟨2, 8, 4, 7, 0, 7, -67202314309290537754231568787725725012669444915200000⟩,
  ⟨2, 8, 5, 7, 1, 7, 562466580552074170022643218678788372554370252800000⟩,
  ⟨2, 8, 6, 7, 2, 7, 348222208333194538977434809977883654503373209600000⟩,
  ⟨2, 8, 7, 7, 3, 7, -195612089731757680062977726275501140074928537600000⟩,
  ⟨2, 8, 8, 7, 4, 7, -13016565315331025743132743229588398938259456000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1011. -/
namespace LaughlinFock
def collectedFourData_10_3_21 : List CollectedFourTerm := [
  ⟨3, 0, 7, 2, 8, 0, 75858228979172544352508066054612146845339824947200000⟩,
  ⟨3, 0, 7, 3, 7, 0, -42357650824525200546200168178203149581075401932800000⟩,
  ⟨3, 0, 8, 3, 8, 0, -191674600642127805457573931710934814511280947200000000⟩,
  ⟨3, 0, 7, 4, 6, 0, 13911325910197379447092549885199051162117996544000000⟩,
  ⟨3, 0, 8, 4, 7, 0, -68087890214729458606980160945652105796531938918400000⟩,
  ⟨3, 0, 7, 5, 5, 0, 36843338472579346868040453063706692947289518899200000⟩,
  ⟨3, 0, 8, 5, 6, 0, -141776857556475525939154281259800021259609807257600000⟩,
  ⟨3, 0, 7, 6, 4, 0, -13189383896015573905027841731744905485613426278400000⟩,
  ⟨3, 0, 8, 6, 5, 0, 148788487039779867887319887745645098807160156979200000⟩,
  ⟨3, 0, 7, 7, 3, 0, -552629430325250400458723039083877533461425789337600000⟩,
  ⟨3, 0, 8, 7, 4, 0, -294187832045227937384982317694364274789500059648000000⟩
]

def collectedFourData_10_3_22 : List CollectedFourTerm := [
  ⟨3, 1, 6, 1, 8, 1, -586255824410148831562882352638252684243107840000000⟩,
  ⟨3, 1, 6, 2, 7, 1, -784477347980414360079979548489061075003637760000000⟩,
  ⟨3, 1, 7, 2, 8, 1, -3679047175465701104655411024886193948605808640000000⟩,
  ⟨3, 1, 6, 3, 6, 1, 2078635599992359172261721020707162234174832640000000⟩,
  ⟨3, 1, 7, 3, 7, 1, 2054303108870598224114920102311949904495247360000000⟩,
  ⟨3, 1, 8, 3, 8, 1, 4648011874193300005913756959521070456504320000000000⟩,
  ⟨3, 1, 6, 4, 5, 1, -1653765094899193611926588776810803990217359360000000⟩,
  ⟨3, 1, 7, 4, 6, 1, -674685198766589560694327469600862144089292800000000⟩,
  ⟨3, 1, 8, 4, 7, 1, 1651096812757752722112721841553545127568343040000000⟩,
  ⟨3, 1, 6, 5, 4, 1, -1865250401614717268814035688118509377515683840000000⟩,
  ⟨3, 1, 7, 5, 5, 1, -1786864552024879023862479621839385424602071040000000⟩,
  ⟨3, 1, 8, 5, 6, 1, 3438016905738496841792208796492960671266242560000000⟩,
  ⟨3, 1, 6, 6, 3, 1, 6906629206574399721953759691422625196922634240000000⟩,
  ⟨3, 1, 7, 6, 4, 1, 639671743221050368079189097698437976115118080000000⟩,
  ⟨3, 1, 8, 6, 5, 1, -3608045365360493770488098732381438056354283520000000⟩,
  ⟨3, 1, 6, 7, 2, 1, -6815997142960755452370627567740941923369615360000000⟩,
  ⟨3, 1, 7, 7, 3, 1, 26801966933284834934801583858367049946491781120000000⟩,
  ⟨3, 1, 8, 7, 4, 1, 7133905754901924516548849647114995702222028800000000⟩
]

def collectedFourData_10_3_23 : List CollectedFourTerm := [
  ⟨3, 2, 5, 0, 8, 2, -577701285593031941679721595974608392716025856000000⟩,
  ⟨3, 2, 5, 1, 7, 2, 4582058834896630497464691453965878587266433024000000⟩,
  ⟨3, 2, 6, 1, 8, 2, 2506333177319190138368090586555507241383886848000000⟩,
  ⟨3, 2, 5, 2, 6, 2, 3202620877081981118537718191771984520535867392000000⟩,
  ⟨3, 2, 6, 2, 7, 2, 3353760461274569710015571988057668604471017472000000⟩,
  ⟨3, 2, 7, 2, 8, 2, 7864244253837145247268539201033068487381090304000000⟩,
  ⟨3, 2, 5, 3, 5, 2, -1210141556598951846783690009828207645582950400000000⟩,
  ⟨3, 2, 6, 3, 6, 2, -8886484621384075905668116546675756939144593408000000⟩,
  ⟨3, 2, 7, 3, 7, 2, -4391229752994505959805346355398234999982391296000000⟩,
  ⟨3, 2, 8, 3, 8, 2, -6623653522240128290662266899669556834336768000000000⟩,
  ⟨3, 2, 5, 4, 4, 2, 4359665438276912757184270930938354659519102976000000⟩,
  ⟨3, 2, 6, 4, 5, 2, 7070098329528024203810142308457221773162708992000000⟩,
  ⟨3, 2, 7, 4, 6, 2, 1442191128434631759516320380441974645278638080000000⟩,
  ⟨3, 2, 8, 4, 7, 2, -2352897005298726868302692394475380477416964096000000⟩,
  ⟨3, 2, 5, 5, 3, 2, -11370258092957686164650676267472452345221087232000000⟩,
  ⟨3, 2, 6, 5, 4, 2, 7974230311960685188897994408664862904756994048000000⟩,
  ⟨3, 2, 7, 5, 5, 2, 3819559417274437777153353955572035157642706944000000⟩,
  ⟨3, 2, 8, 5, 6, 2, -4899349098837706095366767860241859533648953344000000⟩,
  ⟨3, 2, 5, 6, 2, 2, -168278962488485054700869326970383829909372928000000⟩,
  ⟨3, 2, 6, 6, 3, 2, -29526894579334210866110782198088001706606460928000000⟩,
  ⟨3, 2, 7, 6, 4, 2, -1367347193728593634266975355608447632422207488000000⟩,
  ⟨3, 2, 8, 6, 5, 2, 5141648308895504443853863736780103372502990848000000⟩,
  ⟨3, 2, 5, 7, 1, 2, 7844586210209216423638057050467079205920178176000000⟩,
  ⟨3, 2, 6, 7, 2, 2, 29139428666833764111700276834800199234530312192000000⟩,
  ⟨3, 2, 7, 7, 3, 2, -57291250803256644296100418052585771091867205632000000⟩,
  ⟨3, 2, 8, 7, 4, 2, -10166178843720426186819111787441979277831045120000000⟩
]

def collectedFourData_10_3_24 : List CollectedFourTerm := [
  ⟨3, 3, 4, 0, 7, 3, 33418364528820434026706817323823756008200140226560000⟩,
  ⟨3, 3, 5, 0, 8, 3, 3150267108134285169803884380219374125149742694400000⟩,
  ⟨3, 3, 4, 1, 6, 3, 74874993126236096052233431173833399701195708170240000⟩,
  ⟨3, 3, 5, 1, 7, 3, -24986458564469338417173533965019273085475985817600000⟩,
  ⟨3, 3, 6, 1, 8, 3, -6833651895398840926774996117478413202995386777600000⟩,
  ⟨3, 3, 4, 2, 5, 3, -9501244228492302538199593280267849332686764113920000⟩,
  ⟨3, 3, 5, 2, 6, 3, -17464235341866499796281628109942988942984662220800000⟩,
  ⟨3, 3, 6, 2, 7, 3, -9144207857239689475448652307821775304970888806400000⟩,
  ⟨3, 3, 7, 2, 8, 3, -14294855963934887370683036914059123079483962163200000⟩,
  ⟨3, 3, 4, 3, 4, 3, 6518802588688082093412498186259192552953395281920000⟩,
  ⟨3, 3, 5, 3, 5, 3, 6599031778208119765522408798733182880930856960000000⟩,
  ⟨3, 3, 6, 3, 6, 3, 24229477160458196907283807112829625536379197849600000⟩,
  ⟨3, 3, 7, 3, 7, 3, 7981949033815161331562291467765216124135591116800000⟩,
  ⟨3, 3, 8, 3, 8, 3, 9029873373646238172270954961100254405774540800000000⟩,
  ⟨3, 3, 4, 4, 3, 3, 14570473030557461375101954863568252304743622246400000⟩,
  ⟨3, 3, 5, 4, 4, 3, -23773723505868648806568290183794240925469140582400000⟩,
  ⟨3, 3, 6, 4, 5, 3, -19277002470163739344036447827896943454296893030400000⟩,
  ⟨3, 3, 7, 4, 6, 3, -2621474332181226843348621441828296547436068864000000⟩,
  ⟨3, 3, 8, 4, 7, 3, 3207649969573498777416222428370710800994245017600000⟩,
  ⟨3, 3, 4, 5, 2, 3, -99831949019504462618697693334020067925816078499840000⟩,
  ⟨3, 3, 5, 5, 3, 3, 62003237615219017222075292218029402739312479436800000⟩,
  ⟨3, 3, 6, 5, 4, 3, -21742166835122711889164746089258691176429099417600000⟩,
  ⟨3, 3, 7, 5, 5, 3, -6942822470066153105983815237069296225836282675200000⟩,
  ⟨3, 3, 8, 5, 6, 3, 6679169106180858664996906006375025995642463846400000⟩,
  ⟨3, 3, 4, 6, 1, 3, 53570433766794713375732053711604866121164872744960000⟩,
  ⟨3, 3, 5, 6, 2, 3, 917643241825653741027727460991819739936535347200000⟩,
  ⟨3, 3, 6, 6, 3, 3, 80506662455440998694337368221511903265060133273600000⟩,
  ⟨3, 3, 7, 6, 4, 3, 2485430329494644239072739160087009943932528230400000⟩,
  ⟨3, 3, 8, 6, 5, 3, -7009490005063937456544637035777224172454595788800000⟩,
  ⟨3, 3, 4, 7, 0, 3, 1022189902498481884632772659283997535869329546936320000⟩,
  ⟨3, 3, 5, 7, 1, 3, -42777370470237975702618538072196396497221609062400000⟩,
  ⟨3, 3, 6, 7, 2, 3, -79450215853958728135719725054446837376945120870400000⟩,
  ⟨3, 3, 7, 7, 3, 3, 104138446339154369974440205553712897020233619865600000⟩,
  ⟨3, 3, 8, 7, 4, 3, 13859316062412354490860426583337177163101110272000000⟩
]

def collectedFourData_10_3_25 : List CollectedFourTerm := [
  ⟨3, 4, 3, 0, 6, 4, -279355392552228410228541361311164837384568176640000⟩,
  ⟨3, 4, 4, 0, 7, 4, 4007613878551605664205826706428621725227643043840000⟩,
  ⟨3, 4, 5, 0, 8, 4, 188893956387596129943748694208735541870775500800000⟩,
  ⟨3, 4, 3, 1, 5, 4, 3745157916549010163537227400389990800179928760320000⟩,
  ⟨3, 4, 4, 1, 6, 4, 8979196493903090756996940782218186199934550671360000⟩,
  ⟨3, 4, 5, 1, 7, 4, -1498219310410347712143565071404426904567231283200000⟩,
  ⟨3, 4, 6, 1, 8, 4, -273169543785546276425745224870753717671742668800000⟩,
  ⟨3, 4, 3, 2, 4, 4, -4877000459407287876365122039375420274998341795840000⟩,
  ⟨3, 4, 4, 2, 5, 4, -1139412977579310269723238657842409966563890298880000⟩,
  ⟨3, 4, 5, 2, 6, 4, -1047177396637639403244168363187904109352688025600000⟩,
  ⟨3, 4, 6, 2, 7, 4, -365532094241476502565488507142156382511510323200000⟩,
  ⟨3, 4, 7, 2, 8, 4, -428568722322987255131459575244929180883956531200000⟩,
  ⟨3, 4, 3, 3, 3, 4, 6518802588688082093412498186259192552953395281920000⟩,
  ⟨3, 4, 4, 3, 4, 4, 781751114822931733013575882042896773236528250880000⟩,
  ⟨3, 4, 5, 3, 5, 4, 395686199971609113435329790843727853094174720000000⟩,
  ⟨3, 4, 6, 3, 6, 4, 968553172358859265249834066193381477470489804800000⟩,
  ⟨3, 4, 7, 3, 7, 4, 239303824235787031279822888553665247826463948800000⟩,
  ⟨3, 4, 8, 3, 8, 4, 216577001083216128093562864950291462346506240000000⟩,
  ⟨3, 4, 3, 4, 2, 4, -8923945036603617355483947875138390364298149888000000⟩,
  ⟨3, 4, 4, 4, 3, 4, 1747327577445186360580777395153293542224927129600000⟩,
  ⟨3, 4, 5, 4, 4, 4, -1425502199319187923852516986221190464884493516800000⟩,
  ⟨3, 4, 6, 4, 5, 4, -770582120794453729729332752159892850915619635200000⟩,
  ⟨3, 4, 7, 4, 6, 4, -78593440044439477160384346853860892395700224000000⟩,
  ⟨3, 4, 8, 4, 7, 4, 76933881815263879876702618128961357372226273280000⟩,
  ⟨3, 4, 3, 5, 1, 4, 7410643082526994307340877828301344111081983836160000⟩,
  ⟨3, 4, 4, 5, 2, 4, -11972097080585179790864888739655828664393410805760000⟩,
  ⟨3, 4, 5, 5, 3, 4, 3717791685580363373224750995259033773112138137600000⟩,
  ⟨3, 4, 6, 5, 4, 4, -869125013414670448121814709783575335564790988800000⟩,
  ⟨3, 4, 7, 5, 5, 4, -208150159946944315273717238819052543523631923200000⟩,
  ⟨3, 4, 8, 5, 6, 4, 160196533759387681059965476394832572859725905920000⟩,
  ⟨3, 4, 3, 6, 0, 4, 4035840009038081717422744560879387247083320770560000⟩,
  ⟨3, 4, 4, 6, 1, 4, 6424300436925479602426039904770192009890040381440000⟩,
  ⟨3, 4, 5, 6, 2, 4, 55023036634961618248891251800981547065435750400000⟩,
  ⟨3, 4, 6, 6, 3, 4, 3218186789622277034997223356149881014223424716800000⟩,
  ⟨3, 4, 7, 6, 4, 4, 74514755757015248439775825727628686441997926400000⟩,
  ⟨3, 4, 8, 6, 5, 4, -168119115473988387656899058549190505301425520640000⟩,
  ⟨3, 4, 4, 7, 0, 4, 122583570366985401466256178404280944575566556692480000⟩,
  ⟨3, 4, 5, 7, 1, 4, -2564984642450431646724325939958803618664860876800000⟩,
  ⟨3, 4, 6, 7, 2, 4, -3175956216485384848567114045712895437402485555200000⟩,
  ⟨3, 4, 7, 7, 3, 4, 3122135753229870620708030406692192268467149209600000⟩,
  ⟨3, 4, 8, 7, 4, 4, 332408770938243360142005833706311513351494041600000⟩
]

def collectedFourData_10_3_26 : List CollectedFourTerm := [
  ⟨3, 5, 2, 0, 5, 5, -1761838728463069523488898964768191685643468800000000⟩,
  ⟨3, 5, 3, 0, 6, 5, -282793517334747371428879717739385812491960320000000⟩,
  ⟨3, 5, 4, 0, 7, 5, 2028468493987046042158789697292195117095976960000000⟩,
  ⟨3, 5, 5, 0, 8, 5, 63739580183854429940908680437002022997196800000000⟩,
  ⟨3, 5, 2, 1, 4, 5, 6072255640431988549655124949604619430542704640000000⟩,
  ⟨3, 5, 3, 1, 5, 5, 3791250888407167040769499753858705752493916160000000⟩,
  ⟨3, 5, 4, 1, 6, 5, 4544853307021709971686843742344616244768931840000000⟩,
  ⟨3, 5, 5, 1, 7, 5, -505552806956666928026772611827882186191667200000000⟩,
  ⟨3, 5, 6, 1, 8, 5, -69132884289498823125019553086785740970393600000000⟩,
  ⟨3, 5, 2, 2, 3, 5, -2263092388647213474987094402114861430766305280000000⟩,
  ⟨3, 5, 3, 2, 4, 5, -4937023414363167784704599840670843001550929920000000⟩,
  ⟨3, 5, 4, 2, 5, 5, -576718066336000049321161697387498189849886720000000⟩,
  ⟨3, 5, 5, 2, 6, 5, -353355125363278812231858383238442912422297600000000⟩,
  ⟨3, 5, 6, 2, 7, 5, -92507706478189223947596051406086157526630400000000⟩,
  ⟨3, 5, 7, 2, 8, 5, -86768653576441904502854497877752494025605120000000⟩,
  ⟨3, 5, 2, 3, 2, 5, -1210141556598951846783690009828207645582950400000000⟩,
  ⟨3, 5, 3, 3, 3, 5, 6599031778208119765522408798733182880930856960000000⟩,
  ⟨3, 5, 4, 3, 4, 5, 395686199971609113435329790843727853094174720000000⟩,
  ⟨3, 5, 5, 3, 5, 5, 133518682932257042496773091562594888581120000000000⟩,
  ⟨3, 5, 6, 3, 6, 5, 245118373977585786447320688001061188376985600000000⟩,
  ⟨3, 5, 7, 3, 7, 5, 48449804064292116189313925142237724677242880000000⟩,
  ⟨3, 5, 8, 3, 8, 5, 36540415031057254212050622120600293867520000000000⟩,
  ⟨3, 5, 2, 4, 1, 5, -2793535936628671490266670158015556160816414720000000⟩,
  ⟨3, 5, 3, 4, 2, 5, -9033775157682979453530795868482135700537344000000000⟩,
  ⟨3, 5, 4, 4, 3, 5, 884416275353167072155496305366485688542822400000000⟩,
  ⟨3, 5, 5, 4, 4, 5, -481015451597225752212754861324317882109132800000000⟩,
  ⟨3, 5, 6, 4, 5, 5, -195016486297101942948304913728956231214694400000000⟩,
  ⟨3, 5, 7, 4, 6, 5, -15912143414556992120280123605060138985062400000000⟩,
  ⟨3, 5, 8, 4, 7, 5, 12980122346416160349417186815754439690813440000000⟩,
  ⟨3, 5, 2, 5, 0, 5, 20842781567568173224511360896549310410512138240000000⟩,
  ⟨3, 5, 3, 5, 1, 5, 7501848465761811420709432496133830449645486080000000⟩,
  ⟨3, 5, 4, 5, 2, 5, -6059720938908963887671546683023420164606525440000000⟩,
  ⟨3, 5, 5, 5, 3, 5, 1254515950545666803992145219911427848509849600000000⟩,
  ⟨3, 5, 6, 5, 4, 5, -219955409936459758491498575472468755585433600000000⟩,
  ⟨3, 5, 7, 5, 5, 5, -42142387392204348259002028074357143969464320000000⟩,
  ⟨3, 5, 8, 5, 6, 5, 27028021446541469054059308758020659515228160000000⟩,
  ⟨3, 5, 3, 6, 0, 5, 4085510507347009711171572817956253149199073280000000⟩,
  ⟨3, 5, 4, 6, 1, 5, 3251683277661536875279828204813799799505551360000000⟩,
  ⟨3, 5, 5, 6, 2, 5, 18566741480902113955300621604162443306598400000000⟩,
  ⟨3, 5, 6, 6, 3, 5, 814448535754820791517966467359422996388249600000000⟩,
  ⟨3, 5, 7, 6, 4, 5, 15086366997498552550203872616116596129136640000000⟩,
  ⟨3, 5, 8, 6, 5, 5, -28364702730893271356892014185255917028638720000000⟩,
  ⟨3, 5, 4, 7, 0, 5, 62046124677994482285621133509225427995061125120000000⟩,
  ⟨3, 5, 5, 7, 1, 5, -865517602650839712627807843396033113279692800000000⟩,
  ⟨3, 5, 6, 7, 2, 5, -803760955852267759566116289669134501176934400000000⟩,
  ⟨3, 5, 7, 7, 3, 5, 632112194567624023138278592651049256836136960000000⟩,
  ⟨3, 5, 8, 7, 4, 5, 56083307042283865539288590812912871591116800000000⟩
]

def collectedFourData_10_3_27 : List CollectedFourTerm := [
  ⟨3, 6, 1, 0, 4, 6, 525325323911452675495800683308782892785598464000000⟩,
  ⟨3, 6, 2, 0, 5, 6, -12937786228784652311527062006586303816113586176000000⟩,
  ⟨3, 6, 3, 0, 6, 6, -1038324908816919579454359588786445876118893363200000⟩,
  ⟨3, 6, 4, 0, 7, 6, 4965246690488874365426047425483780299147339366400000⟩,
  ⟨3, 6, 5, 0, 8, 6, 117015401212482868104486063147880141956317184000000⟩,
  ⟨3, 6, 1, 1, 3, 6, -2121626374634792156747049428727088136283645542400000⟩,
  ⟨3, 6, 2, 1, 4, 6, 44590656416648105849740133776677487341074173132800000⟩,
  ⟨3, 6, 3, 1, 5, 6, 13920227981561816846715814366708504647247174041600000⟩,
  ⟨3, 6, 4, 1, 6, 6, 11124805688794233614242718037319143408119945625600000⟩,
  ⟨3, 6, 5, 1, 7, 6, -928111926208076543531860158528943462218203136000000⟩,
  ⟨3, 6, 6, 1, 8, 6, -101533297442846975263424348387442517097211494400000⟩,
  ⟨3, 6, 1, 2, 2, 6, -370389902034588453279375256794355477440469401600000⟩,
  ⟨3, 6, 2, 2, 3, 6, -16618663823929567963978891547956456444307020185600000⟩,
  ⟨3, 6, 3, 2, 4, 6, -18127128354493446862996006654179554102575575859200000⟩,
  ⟨3, 6, 4, 2, 5, 6, -1411679539863858584872937935840654749571271884800000⟩,
  ⟨3, 6, 5, 2, 6, 6, -648701978356376351279268996016718972492709888000000⟩,
  ⟨3, 6, 6, 2, 7, 6, -135863165180167256930797359903003409835989401600000⟩,
  ⟨3, 6, 7, 2, 8, 6, -106195331918069982720508054981774502412052070400000⟩,
  ⟨3, 6, 1, 3, 1, 6, 2078635599992359172261721020707162234174832640000000⟩,
  ⟨3, 6, 2, 3, 2, 6, -8886484621384075905668116546675756939144593408000000⟩,
  ⟨3, 6, 3, 3, 3, 6, 24229477160458196907283807112829625536379197849600000⟩,
  ⟨3, 6, 4, 3, 4, 6, 968553172358859265249834066193381477470489804800000⟩,
  ⟨3, 6, 5, 3, 5, 6, 245118373977585786447320688001061188376985600000000⟩,
  ⟨3, 6, 6, 3, 6, 6, 359997662900253369415577307138122223643420262400000⟩,
  ⟨3, 6, 7, 3, 7, 6, 59297255539872613031513885012058338775112089600000⟩,
  ⟨3, 6, 8, 3, 8, 6, 38332686247889521090509183563195877634867200000000⟩,
  ⟨3, 6, 1, 4, 0, 6, -16632209830299319265953396621137803671443288883200000⟩,
  ⟨3, 6, 2, 4, 1, 6, -20513892779538277144963979590008219218198554214400000⟩,
  ⟨3, 6, 3, 4, 2, 6, -33169055129967774047014535248358321702767165440000000⟩,
  ⟨3, 6, 4, 4, 3, 6, 2164857377488976322559063849542070011602927616000000⟩,
  ⟨3, 6, 5, 4, 4, 6, -883065371558732017879124373470300856190500864000000⟩,
  ⟨3, 6, 6, 4, 5, 6, -286414592895413640298386808443532506339842457600000⟩,
  ⟨3, 6, 7, 4, 6, 6, -19474721362918538727608628910183762895044608000000⟩,
  ⟨3, 6, 8, 4, 7, 6, 13616784509466854005023000452591433682413158400000⟩,
  ⟨3, 6, 2, 5, 0, 6, 153055695721756589542803891214884193787177651404800000⟩,
  ⟨3, 6, 3, 5, 1, 6, 27544323496461522485590496525462864476966276300800000⟩,
  ⟨3, 6, 4, 5, 2, 6, -14832869934333824439992631794140088273867479449600000⟩,
  ⟨3, 6, 5, 5, 3, 6, 2303085254988001026601789896789231019279515648000000⟩,
  ⟨3, 6, 6, 5, 4, 6, -323041607344512672493198201575175894518359654400000⟩,
  ⟨3, 6, 7, 5, 5, 6, -51577668114814450444980421638427841820780134400000⟩,
  ⟨3, 6, 8, 5, 6, 6, 28353719166323495440036674465782930549086617600000⟩,
  ⟨3, 6, 3, 6, 0, 6, 15000652649297549716727066745756862319178861772800000⟩,
  ⟨3, 6, 4, 6, 1, 6, 7959408628128323965498634691664730403721602662400000⟩,
  ⟨3, 6, 5, 6, 2, 6, 34085488127305532897148721730033258009198592000000⟩,
  ⟨3, 6, 6, 6, 3, 6, 1196155003260097516759374833638368588163606118400000⟩,
  ⟨3, 6, 7, 6, 4, 6, 18464061440411169080038620688114818659175628800000⟩,
  ⟨3, 6, 8, 6, 5, 6, -29755963345622876158435982413983106160866099200000⟩,
  ⟨3, 6, 4, 7, 0, 6, 151875326695135529876843514207512351047502580940800000⟩,
  ⟨3, 6, 5, 7, 1, 6, -1588948173780234728092404959144972517233393664000000⟩,
  ⟨3, 6, 6, 7, 2, 6, -1180458490083445022523170130883695317874219417600000⟩,
  ⟨3, 6, 7, 7, 3, 6, 773636117937801677624070206674511219595096883200000⟩,
  ⟨3, 6, 8, 7, 4, 6, 58834137783292649823078539768444025147752448000000⟩
]

def collectedFourData_10_3_28 : List CollectedFourTerm := [
  ⟨3, 7, 0, 0, 3, 7, -18758641415859994034370653273875794453934689484800000⟩,
  ⟨3, 7, 1, 0, 4, 7, 519175870019602365866598049636661474975809536000000⟩,
  ⟨3, 7, 2, 0, 5, 7, -6393168305159697595978563019699462102069542912000000⟩,
  ⟨3, 7, 3, 0, 6, 7, -342056762010654025027306544929480794518952345600000⟩,
  ⟨3, 7, 4, 0, 7, 7, 1226780888460949827511099969427930954678560358400000⟩,
  ⟨3, 7, 5, 0, 8, 7, 23129123978962695827376862010442049622586163200000⟩,
  ⟨3, 7, 0, 1, 2, 7, 7337486323251304605788679354088548509204820787200000⟩,
  ⟨3, 7, 1, 1, 3, 7, -2096790633861043880210885476445880197670607257600000⟩,
  ⟨3, 7, 2, 1, 4, 7, 22034339280929667099762772414620856694722894233600000⟩,
  ⟨3, 7, 3, 1, 5, 7, 4585759302691157891102672344387562776080207052800000⟩,
  ⟨3, 7, 4, 1, 6, 7, 2748644701379515323081713504088041098338474393600000⟩,
  ⟨3, 7, 5, 1, 7, 7, -183449491136988072620163932785607176107117772800000⟩,
  ⟨3, 7, 6, 1, 8, 7, -16724124917284717840853946292710521750264217600000⟩,
  ⟨3, 7, 0, 2, 1, 7, 7580443014361630210730686989804950473452552192000000⟩,
  ⟨3, 7, 1, 2, 2, 7, -366054120908315209503239963700906808593245798400000⟩,
  ⟨3, 7, 2, 2, 3, 7, -8212062941407178191886401766045260570707571507200000⟩,
  ⟨3, 7, 3, 2, 4, 7, -5971644113358003413707880304838971098549295513600000⟩,
  ⟨3, 7, 4, 2, 5, 7, -348788607714839534990680188926351440838708428800000⟩,
  ⟨3, 7, 5, 2, 6, 7, -128221655673838171375896983342841702008645222400000⟩,
  ⟨3, 7, 6, 2, 7, 7, -22378792015592917550495521452614718939620966400000⟩,
  ⟨3, 7, 7, 2, 8, 7, -14993172891709635741047961848479215279459532800000⟩,
  ⟨3, 7, 0, 3, 0, 7, -42357650824525200546200168178203149581075401932800000⟩,
  ⟨3, 7, 1, 3, 1, 7, 2054303108870598224114920102311949904495247360000000⟩,
  ⟨3, 7, 2, 3, 2, 7, -4391229752994505959805346355398234999982391296000000⟩,
  ⟨3, 7, 3, 3, 3, 7, 7981949033815161331562291467765216124135591116800000⟩,
  ⟨3, 7, 4, 3, 4, 7, 239303824235787031279822888553665247826463948800000⟩,
  ⟨3, 7, 5, 3, 5, 7, 48449804064292116189313925142237724677242880000000⟩,
  ⟨3, 7, 6, 3, 6, 7, 59297255539872613031513885012058338775112089600000⟩,
  ⟨3, 7, 7, 3, 7, 7, 8371874622503227502109082400414357622305587200000⟩,
  ⟨3, 7, 8, 3, 8, 7, 4735495517509787131151624083523472300441600000000⟩,
  ⟨3, 7, 1, 4, 0, 7, -16437513319745708525063021367153836241669901516800000⟩,
  ⟨3, 7, 2, 4, 1, 7, -10136878660261208952331173464248857904318041292800000⟩,
  ⟨3, 7, 3, 4, 2, 7, -10926926148422156491750404619056520246088171520000000⟩,
  ⟨3, 7, 4, 4, 3, 7, 534878893738445780663415480530621623588356096000000⟩,
  ⟨3, 7, 5, 4, 4, 7, -174545643126264314830611527889697083948741427200000⟩,
  ⟨3, 7, 6, 4, 5, 7, -47176971007096980891214494586964712473650790400000⟩,
  ⟨3, 7, 7, 4, 6, 7, -2749535776557281062995423754349369471533056000000⟩,
  ⟨3, 7, 8, 4, 7, 7, 1682173317843781011326551317151878338523955200000⟩,
  ⟨3, 7, 2, 5, 0, 7, 75632013507493248065393733196401394157016947097600000⟩,
  ⟨3, 7, 3, 5, 1, 7, 9073963291229171278868689583011918445948593766400000⟩,
  ⟨3, 7, 4, 5, 2, 7, -3664809120425822878802474056244272816998422937600000⟩,
  ⟨3, 7, 5, 5, 3, 7, 455225071612674816731200994926311049150228070400000⟩,
  ⟨3, 7, 6, 5, 4, 7, -53210014160637140281702263333141347237992857600000⟩,
  ⟨3, 7, 7, 5, 5, 7, -7281985765563082097078647738070054491442380800000⟩,
  ⟨3, 7, 8, 5, 6, 7, 3502726345567516319245186527488891486522572800000⟩,
  ⟨3, 7, 3, 6, 0, 7, 4941685044531648171744073917649853395881059942400000⟩,
  ⟨3, 7, 4, 6, 1, 7, 1966558964158458523819354612584742419226322534400000⟩,
  ⟨3, 7, 5, 6, 2, 7, 6737296737105148583703723867118418381085081600000⟩,
  ⟨3, 7, 6, 6, 3, 7, 197025470449411744635505709935968926033353113600000⟩,
  ⟨3, 7, 7, 6, 4, 7, 2606845898582555771691690135699664206928281600000⟩,
  ⟨3, 7, 8, 6, 5, 7, -3675955035635956360467275966671313559984537600000⟩,
  ⟨3, 7, 4, 7, 0, 7, 37524368844604309933905906220181958196990889164800000⟩,
  ⟨3, 7, 5, 7, 1, 7, -314069591922989727246281736341680676276482867200000⟩,
  ⟨3, 7, 6, 7, 2, 7, -194440008795515309008492682509962034754774630400000⟩,
  ⟨3, 7, 7, 7, 3, 7, 109225705706738510246943614324995315384870502400000⟩,
  ⟨3, 7, 8, 7, 4, 7, 7268178231695799401978452303322774916562944000000⟩
]

def collectedFourData_10_3_29 : List CollectedFourTerm := [
  ⟨3, 8, 0, 0, 3, 8, -84885611736805918588385660890005403080012595200000000⟩,
  ⟨3, 8, 1, 0, 4, 8, 1174673590389700352993643468782172773548032000000000⟩,
  ⟨3, 8, 2, 0, 5, 8, -9643342331124427331113167713756062307844096000000000⟩,
  ⟨3, 8, 3, 0, 6, 8, -386964290860589679863852985379830611155353600000000⟩,
  ⟨3, 8, 4, 0, 7, 8, 1110272795086166481596233328713753598172856320000000⟩,
  ⟨3, 8, 5, 0, 8, 8, 17443781369571229629212453428250628902092800000000⟩,
  ⟨3, 8, 0, 1, 2, 8, 33203204931090117028054315511679952693808332800000000⟩,
  ⟨3, 8, 1, 1, 3, 8, -4744143024366774978962636550340284840620851200000000⟩,
  ⟨3, 8, 2, 1, 4, 8, 33236208806619097940452209303286264783228108800000000⟩,
  ⟨3, 8, 3, 1, 5, 8, 5187808848427224156253008669092067301706956800000000⟩,
  ⟨3, 8, 4, 1, 6, 8, 2487604317938115037956005972522660693048033280000000⟩,
  ⟨3, 8, 5, 1, 7, 8, -138355988694744858085571476583901625004851200000000⟩,
  ⟨3, 8, 6, 1, 8, 8, -10811303615792327058997160318655291142963200000000⟩,
  ⟨3, 8, 0, 2, 1, 8, 34302619696437327819955230726096229402411008000000000⟩,
  ⟨3, 8, 1, 2, 2, 8, -828224371190596648853903983075706075401420800000000⟩,
  ⟨3, 8, 2, 2, 3, 8, -12386930925127874628902857371613666075056537600000000⟩,
  ⟨3, 8, 3, 2, 4, 8, -6755642005186904691508153492381181717092761600000000⟩,
  ⟨3, 8, 4, 2, 5, 8, -315663951096915113360197735345926074259210240000000⟩,
  ⟨3, 8, 5, 2, 6, 8, -96703642146293970226782442560489678018969600000000⟩,
  ⟨3, 8, 6, 2, 7, 8, -14466760815998826316349224261782355102924800000000⟩,
  ⟨3, 8, 7, 2, 8, 8, -8480789097234579536139313888978679522918400000000⟩,
  ⟨3, 8, 0, 3, 0, 8, -191674600642127805457573931710934814511280947200000000⟩,
  ⟨3, 8, 1, 3, 1, 8, 4648011874193300005913756959521070456504320000000000⟩,
  ⟨3, 8, 2, 3, 2, 8, -6623653522240128290662266899669556834336768000000000⟩,
  ⟨3, 8, 3, 3, 3, 8, 9029873373646238172270954961100254405774540800000000⟩,
  ⟨3, 8, 4, 3, 4, 8, 216577001083216128093562864950291462346506240000000⟩,
  ⟨3, 8, 5, 3, 5, 8, 36540415031057254212050622120600293867520000000000⟩,
  ⟨3, 8, 6, 3, 6, 8, 38332686247889521090509183563195877634867200000000⟩,
  ⟨3, 8, 7, 3, 7, 8, 4735495517509787131151624083523472300441600000000⟩,
  ⟨3, 8, 8, 3, 8, 8, 2380979310159184940653316100836661657600000000000⟩,
  ⟨3, 8, 1, 4, 0, 8, -37191082836063203111778937802750625486313881600000000⟩,
  ⟨3, 8, 2, 4, 1, 8, -15290289012268849719839953344146005853365862400000000⟩,
  ⟨3, 8, 3, 4, 2, 8, -12361487033483976822642700276294222998405120000000000⟩,
  ⟨3, 8, 4, 4, 3, 8, 484081134593322514097142593483980921425100800000000⟩,
  ⟨3, 8, 5, 4, 4, 8, -131640785032547071340359668610358039071948800000000⟩,
  ⟨3, 8, 6, 4, 5, 8, -30497533339039826965647746229517977177292800000000⟩,
  ⟨3, 8, 7, 4, 6, 8, -1555256729492997914121486802721144045568000000000⟩,
  ⟨3, 8, 8, 4, 7, 8, 845786856112169307532632218097541133107200000000⟩,
  ⟨3, 8, 2, 5, 0, 8, 114081995441345649656993879681903357078588620800000000⟩,
  ⟨3, 8, 3, 5, 1, 8, 10265254660207981431600962753164918535906918400000000⟩,
  ⟨3, 8, 4, 5, 2, 8, -3316760070086446996596671185475915364150804480000000⟩,
  ⟨3, 8, 5, 5, 3, 8, 343326735175165940555739668921430826391961600000000⟩,
  ⟨3, 8, 6, 5, 4, 8, -34397591583204725679805130804039781659443200000000⟩,
  ⟨3, 8, 7, 5, 5, 8, -4119007092951810003035247254870512002662400000000⟩,
  ⟨3, 8, 8, 5, 6, 8, 1761150216932606618501204226283500522700800000000⟩,
  ⟨3, 8, 3, 6, 0, 8, 5590462932739829408110298141041835161052774400000000⟩,
  ⟨3, 8, 4, 6, 1, 8, 1779793717341945115068867457241199135550341120000000⟩,
  ⟨3, 8, 5, 6, 2, 8, 5081209794667657166382698457293040019046400000000⟩,
  ⟨3, 8, 6, 6, 3, 8, 127367033647985147618578255071690930467635200000000⟩,
  ⟨3, 8, 7, 6, 4, 8, 1474545143616274564637424979585767623884800000000⟩,
  ⟨3, 8, 8, 6, 5, 8, -1848248584031437090096397713235607394713600000000⟩,
  ⟨3, 8, 4, 7, 0, 8, 33960657744848183001014907483545605363508183040000000⟩,
  ⟨3, 8, 5, 7, 1, 8, -236868516996932611215227265481087646485708800000000⟩,
  ⟨3, 8, 6, 7, 2, 8, -125695663034245365330039175390050032340172800000000⟩,
  ⟨3, 8, 7, 7, 3, 8, 61782798129918361306018295536592698422067200000000⟩,
  ⟨3, 8, 8, 7, 4, 8, 3654397291313939681059165622723237904384000000000⟩
]

def collectedFourData_10_3_30 : List CollectedFourTerm := [
  ⟨4, 0, 6, 1, 8, 1, 4690927974995016723323773548169308780331479859200000⟩,
  ⟨4, 0, 6, 2, 7, 1, 6276998170711090011585414997420676174534462668800000⟩,
  ⟨4, 0, 7, 2, 8, 1, 29437908500239536178676746245867992716225491763200000⟩,
  ⟨4, 0, 6, 3, 6, 1, -16632209830299319265953396621137803671443288883200000⟩,
  ⟨4, 0, 7, 3, 7, 1, -16437513319745708525063021367153836241669901516800000⟩,
  ⟨4, 0, 8, 3, 8, 1, -37191082836063203111778937802750625486313881600000000⟩,
  ⟨4, 0, 6, 4, 5, 1, 13232607037274528867168128877485895670318288076800000⟩,
  ⟨4, 0, 7, 4, 6, 1, 5398495914976328714245127399174677937063460864000000⟩,
  ⟨4, 0, 8, 4, 7, 1, -13211256768635307822410252401584094821792035635200000⟩,
  ⟨4, 0, 6, 5, 4, 1, 14924807438985501689059123737977830267524690739200000⟩,
  ⟨4, 0, 7, 5, 5, 1, 14297602796618526023202848904040620552025748275200000⟩,
  ⟨4, 0, 8, 5, 6, 1, -27509303976401284155301188903067437970576166092800000⟩,
  ⟨4, 0, 6, 6, 3, 1, -55263417110840099686797106905088705710156624691200000⟩,
  ⟨4, 0, 7, 6, 4, 1, -5118335631221251186301590582316965060936099430400000⟩,
  ⟨4, 0, 8, 6, 5, 1, 28869787274948669475718023230952976538882644377600000⟩,
  ⟨4, 0, 6, 7, 2, 1, 54538224345267957778693925892147925884911537356800000⟩,
  ⟨4, 0, 7, 7, 3, 1, -214456029667141249982071994847294135666365536665600000⟩,
  ⟨4, 0, 8, 7, 4, 1, -57081971186072647159893689851753549778380652544000000⟩
]

def collectedFourData_10_3_31 : List CollectedFourTerm := [
  ⟨4, 1, 5, 0, 8, 2, -1333587209810654255606524636950853960063569100800000⟩,
  ⟨4, 1, 5, 1, 7, 2, 10577395635436956473047928391708469627184165683200000⟩,
  ⟨4, 1, 6, 1, 8, 2, 5785713053011225150900075777029060010365576806400000⟩,
  ⟨4, 1, 5, 2, 6, 2, 7393049567415788191060041576429762100546083225600000⟩,
  ⟨4, 1, 6, 2, 7, 2, 7741945824706318642978153194305564264208374169600000⟩,
  ⟨4, 1, 7, 2, 8, 2, 18154114960949375588745686148890191516241441587200000⟩,
  ⟨4, 1, 5, 3, 5, 2, -2793535936628671490266670158015556160816414720000000⟩,
  ⟨4, 1, 6, 3, 6, 2, -20513892779538277144963979590008219218198554214400000⟩,
  ⟨4, 1, 7, 3, 7, 2, -10136878660261208952331173464248857904318041292800000⟩,
  ⟨4, 1, 8, 3, 8, 2, -15290289012268849719839953344146005853365862400000000⟩,
  ⟨4, 1, 5, 4, 4, 2, 10064014418059272937423579101541063629269159116800000⟩,
  ⟨4, 1, 6, 4, 5, 2, 16320878868537470707380847724883507747053214105600000⟩,
  ⟨4, 1, 7, 4, 6, 2, 3329207829282382329346864397183010707387449344000000⟩,
  ⟨4, 1, 8, 4, 7, 2, -5431515266660885653130238005369588287089200332800000⟩,
  ⟨4, 1, 5, 5, 3, 2, -26247528165786975470143282992494691984256637337600000⟩,
  ⟨4, 1, 6, 5, 4, 2, 18408010882646132213762527110232514531045041766400000⟩,
  ⟨4, 1, 7, 5, 5, 2, 8817213520236737407158303329996082794252677939200000⟩,
  ⟨4, 1, 8, 5, 6, 2, -11309840323274031224213781677261583907887985459200000⟩,
  ⟨4, 1, 5, 6, 2, 2, -388461437859672572903256828146495523777832550400000⟩,
  ⟨4, 1, 6, 6, 3, 2, -68160985510021845474906688165998520027075470950400000⟩,
  ⟨4, 1, 7, 6, 4, 2, -3156435296928716986982191530620186459717920358400000⟩,
  ⟨4, 1, 8, 6, 5, 2, 11869172863357619322372067877254045409347004006400000⟩,
  ⟨4, 1, 5, 7, 1, 2, 18108735599320996485968992044996079950670646476800000⟩,
  ⟨4, 1, 6, 7, 2, 2, 67266544735811384890089356719676435510691731865600000⟩,
  ⟨4, 1, 7, 7, 3, 2, -132253261695353549496693924598704476227410434457600000⟩,
  ⟨4, 1, 8, 7, 4, 2, -23467986685741854920973988684356400180327612416000000⟩
]

def collectedFourData_10_3_32 : List CollectedFourTerm := [
  ⟨4, 2, 4, 0, 7, 3, -45748225108991283582428990812933780362215030784000000⟩,
  ⟨4, 2, 5, 0, 8, 3, -4312572767948833790515747869141092180070236160000000⟩,
  ⟨4, 2, 4, 1, 6, 3, -102500469094444042201116123635664536754230132736000000⟩,
  ⟨4, 2, 5, 1, 7, 3, 34205328333707476379558496832048031767084400640000000⟩,
  ⟨4, 2, 6, 1, 8, 3, 9354959455229388598307189775317395892223344640000000⟩,
  ⟨4, 2, 4, 2, 5, 3, 13006772351343203732392896646597637345208434688000000⟩,
  ⟨4, 2, 5, 2, 6, 3, 23907745966654902096694554526412063798061957120000000⟩,
  ⟨4, 2, 6, 2, 7, 3, 12518005755058234096059703202130205481065512960000000⟩,
  ⟨4, 2, 7, 2, 8, 3, 19569009368328377334293363297642165677043220480000000⟩,
  ⟨4, 2, 4, 3, 4, 3, -8923945036603617355483947875138390364298149888000000⟩,
  ⟨4, 2, 5, 3, 5, 3, -9033775157682979453530795868482135700537344000000000⟩,
  ⟨4, 2, 6, 3, 6, 3, -33169055129967774047014535248358321702767165440000000⟩,
  ⟨4, 2, 7, 3, 7, 3, -10926926148422156491750404619056520246088171520000000⟩,
  ⟨4, 2, 8, 3, 8, 3, -12361487033483976822642700276294222998405120000000000⟩,
  ⟨4, 2, 4, 4, 3, 3, -19946316629934647876372252580920975841778728960000000⟩,
  ⟨4, 2, 5, 4, 4, 3, 32545149050828956197976102080544365396476559360000000⟩,
  ⟨4, 2, 6, 4, 5, 3, 26389341934165554061609031135371196486972866560000000⟩,
  ⟨4, 2, 7, 4, 6, 3, 3588679444879538002651975076201916981156249600000000⟩,
  ⟨4, 2, 8, 4, 7, 3, -4391127302245544328064839759130401746599280640000000⟩,
  ⟨4, 2, 4, 5, 2, 3, 136665409609583837927490470324984056025947570176000000⟩,
  ⟨4, 2, 5, 5, 3, 3, -84879619691174533648466819273173532027671019520000000⟩,
  ⟨4, 2, 6, 5, 4, 3, 29764040124483825130433457825349495635459440640000000⟩,
  ⟨4, 2, 7, 5, 5, 3, 9504409019730097107489151822276002820946657280000000⟩,
  ⟨4, 2, 8, 5, 6, 3, -9143479524471132590485387730794305433852968960000000⟩,
  ⟨4, 2, 4, 6, 1, 3, -73335493753324512786982522174967480263108460544000000⟩,
  ⟨4, 2, 5, 6, 2, 3, -1256211971731290400495408851141688224204718080000000⟩,
  ⟨4, 2, 6, 6, 3, 3, -110209968941142904270359928253673738003850199040000000⟩,
  ⟨4, 2, 7, 6, 4, 3, -3402441376458609325133528726924871225374146560000000⟩,
  ⟨4, 2, 8, 6, 5, 3, 9595673850955153053489744348946522584719032320000000⟩,
  ⟨4, 2, 4, 7, 0, 3, -1399331607724520949342133893339837699895798530048000000⟩,
  ⟨4, 2, 5, 7, 1, 3, 58560279697572589293257230060145636351001231360000000⟩,
  ⟨4, 2, 6, 7, 2, 3, 108763741466469246478491622802681042871842242560000000⟩,
  ⟨4, 2, 7, 7, 3, 3, -142560809087936633493702226803872725435510947840000000⟩,
  ⟨4, 2, 8, 7, 4, 3, -18972775000197734782855398540326873691114700800000000⟩
]

def collectedFourData_10_3_33 : List CollectedFourTerm := [
  ⟨4, 3, 3, 0, 6, 4, -624399981092570295947141149314506558022667468800000⟩,
  ⟨4, 3, 4, 0, 7, 4, 8957600593037070686195675972035029531710246092800000⟩,
  ⟨4, 3, 5, 0, 8, 4, 422205498592137252681672776956809115846311936000000⟩,
  ⟨4, 3, 3, 1, 5, 4, 8370973300057879787867644276998430365575439974400000⟩,
  ⟨4, 3, 4, 1, 6, 4, 20069811682519602708417740727679706294020944691200000⟩,
  ⟨4, 3, 5, 1, 7, 4, -3348738324132567226828847728302331454338105344000000⟩,
  ⟨4, 3, 6, 1, 8, 4, -610573708337747067019671004728745897802858496000000⟩,
  ⟨4, 3, 3, 2, 4, 4, -10900806198230218230645375261806671568225225932800000⟩,
  ⟨4, 3, 4, 2, 5, 4, -2546753922153615296155199284169921092617083289600000⟩,
  ⟨4, 3, 5, 2, 6, 4, -2340593967731850842511532142559718731732221952000000⟩,
  ⟨4, 3, 6, 2, 7, 4, -817017458112730108797729643292436355973382144000000⟩,
  ⟨4, 3, 7, 2, 8, 4, -957913501044408699325347505837894437389205504000000⟩,
  ⟨4, 3, 3, 3, 3, 4, 14570473030557461375101954863568252304743622246400000⟩,
  ⟨4, 3, 4, 3, 4, 4, 1747327577445186360580777395153293542224927129600000⟩,
  ⟨4, 3, 5, 3, 5, 4, 884416275353167072155496305366485688542822400000000⟩,
  ⟨4, 3, 6, 3, 6, 4, 2164857377488976322559063849542070011602927616000000⟩,
  ⟨4, 3, 7, 3, 7, 4, 534878893738445780663415480530621623588356096000000⟩,
  ⟨4, 3, 8, 3, 8, 4, 484081134593322514097142593483980921425100800000000⟩,
  ⟨4, 3, 3, 4, 2, 4, -19946316629934647876372252580920975841778728960000000⟩,
  ⟨4, 3, 4, 4, 3, 4, 3905531575214970363523409840856872684598853632000000⟩,
  ⟨4, 3, 5, 4, 4, 4, -3186204992036829543775114256563922676435910656000000⟩,
  ⟨4, 3, 6, 4, 5, 4, -1722363249402365964242277839707172204061917184000000⟩,
  ⟨4, 3, 7, 4, 6, 4, -175667782996432466091505712137075117082542080000000⟩,
  ⟨4, 3, 8, 4, 7, 4, 171958428695260246164209357916121838562941337600000⟩,
  ⟨4, 3, 3, 5, 1, 4, 16563866400927047404107438891115983876146803507200000⟩,
  ⟨4, 3, 4, 5, 2, 4, -26759380309289008651945735398651564876155269939200000⟩,
  ⟨4, 3, 5, 5, 3, 4, 8309805788869767370458142954158221989345492992000000⟩,
  ⟨4, 3, 6, 5, 4, 4, -1942620963873966127271402947669084402819792896000000⟩,
  ⟨4, 3, 7, 5, 5, 4, -465245917567130760623674775917840584507654144000000⟩,
  ⟨4, 3, 8, 5, 6, 4, 358062580201511334129820611876400842351732326400000⟩,
  ⟨4, 3, 3, 6, 0, 4, 9020690104863039840284616925912383072674984755200000⟩,
  ⟨4, 3, 4, 6, 1, 4, 14359246960300936070366759966700162023083003084800000⟩,
  ⟨4, 3, 5, 6, 2, 4, 122984499137966532301023435226256968639315968000000⟩,
  ⟨4, 3, 6, 6, 3, 4, 7193116095716048377655481607120019091049414656000000⟩,
  ⟨4, 3, 7, 6, 4, 4, 166551329690545005549428659107765569231781888000000⟩,
  ⟨4, 3, 8, 6, 5, 4, -375770703991805295260356633239527105745439948800000⟩,
  ⟨4, 3, 4, 7, 0, 4, 273992129953586887453153492424482744295312955801600000⟩,
  ⟨4, 3, 5, 7, 1, 4, -5733114179814342627510100353441590785244921856000000⟩,
  ⟨4, 3, 6, 7, 2, 4, -7098724615289287074676517318160156837317443584000000⟩,
  ⟨4, 3, 7, 7, 3, 4, 6978428042768842317221794413047695511736287232000000⟩,
  ⟨4, 3, 8, 7, 4, 4, 742982007229514695984309888852738932234780672000000⟩
]

def collectedFourData_10_3_34 : List CollectedFourTerm := [
  ⟨4, 4, 2, 0, 5, 5, 6347213985350083409995485689470426073763151872000000⟩,
  ⟨4, 4, 3, 0, 6, 5, 1018794137735447285135455006908872246973746380800000⟩,
  ⟨4, 4, 4, 0, 7, 5, -7307776464369213054302731652623072723523233382400000⟩,
  ⟨4, 4, 5, 0, 8, 5, -229628710180657250885936541811765392747528192000000⟩,
  ⟨4, 4, 2, 1, 4, 5, -21875955671148555179333411720785338158810765721600000⟩,
  ⟨4, 4, 3, 1, 5, 5, -13658390108078107166907508974141587536059197030400000⟩,
  ⟨4, 4, 4, 1, 6, 5, -16373324076521711354112022543178793404354632089600000⟩,
  ⟨4, 4, 5, 1, 7, 5, 1821308497087909857364605444625253546713939968000000⟩,
  ⟨4, 4, 6, 1, 8, 5, 249058669741402412364911031962523038996496384000000⟩,
  ⟨4, 4, 2, 2, 3, 5, 8153034342644724728876465856433924146979877683200000⟩,
  ⟨4, 4, 3, 2, 4, 5, 17786159173026471337253543076169669412960128204800000⟩,
  ⟨4, 4, 4, 2, 5, 5, 2077689017226440595143796987574227197741550796800000⟩,
  ⟨4, 4, 5, 2, 6, 5, 1272999938795446761583160348458995099730182144000000⟩,
  ⟨4, 4, 6, 2, 7, 5, 333268987010652454021077484060007646338482176000000⟩,
  ⟨4, 4, 7, 2, 8, 5, 312593430132406590047517883497318451178687692800000⟩,
  ⟨4, 4, 2, 3, 2, 5, 4359665438276912757184270930938354659519102976000000⟩,
  ⟨4, 4, 3, 3, 3, 5, -23773723505868648806568290183794240925469140582400000⟩,
  ⟨4, 4, 4, 3, 4, 5, -1425502199319187923852516986221190464884493516800000⟩,
  ⟨4, 4, 5, 3, 5, 5, -481015451597225752212754861324317882109132800000000⟩,
  ⟨4, 4, 6, 3, 6, 5, -883065371558732017879124373470300856190500864000000⟩,
  ⟨4, 4, 7, 3, 7, 5, -174545643126264314830611527889697083948741427200000⟩,
  ⟨4, 4, 8, 3, 8, 5, -131640785032547071340359668610358039071948800000000⟩,
  ⟨4, 4, 2, 4, 1, 5, 10064014418059272937423579101541063629269159116800000⟩,
  ⟨4, 4, 3, 4, 2, 5, 32545149050828956197976102080544365396476559360000000⟩,
  ⟨4, 4, 4, 4, 3, 5, -3186204992036829543775114256563922676435910656000000⟩,
  ⟨4, 4, 5, 4, 4, 5, 1732910028723661698253018193063615437348012032000000⟩,
  ⟨4, 4, 6, 4, 5, 5, 702567919073158529341049645829181005769998336000000⟩,
  ⟨4, 4, 7, 4, 6, 5, 57325212339881548812311739633134816257376256000000⟩,
  ⟨4, 4, 8, 4, 7, 5, -46762290303720467203183100851196436491639193600000⟩,
  ⟨4, 4, 2, 5, 0, 5, -75088367920411900960336994642294243489675319705600000⟩,
  ⟨4, 4, 3, 5, 1, 5, -27026217966838459657819441893835322629811286835200000⟩,
  ⟨4, 4, 4, 5, 2, 5, 21830798057387541287936926624149422678059096473600000⟩,
  ⟨4, 4, 5, 5, 3, 5, -4519528977033222425293915885091088077395329024000000⟩,
  ⟨4, 4, 6, 5, 4, 5, 792413080463949100378534514248476347527593984000000⟩,
  ⟨4, 4, 7, 5, 5, 5, 151822494482898039550797154094275959225896140800000⟩,
  ⟨4, 4, 8, 5, 6, 5, -97371361493161759018673689602702543820318310400000⟩,
  ⟨4, 4, 3, 6, 0, 5, -14718492113150988475348976354854646405307511603200000⟩,
  ⟨4, 4, 4, 6, 1, 5, -11714539612775306778849898576749077361997538918400000⟩,
  ⟨4, 4, 5, 6, 2, 5, -66888688099599603851032749465910652065284096000000⟩,
  ⟨4, 4, 6, 6, 3, 5, -2934138666029020214514249230544300088202625024000000⟩,
  ⟨4, 4, 7, 6, 4, 5, -54350263760054438323128234797283243281979801600000⟩,
  ⟨4, 4, 8, 6, 5, 5, 102186899944512876146908564639915418181225676800000⟩,
  ⟨4, 4, 4, 7, 0, 5, -223527854127992912256416690915820672291420556492800000⟩,
  ⟨4, 4, 5, 7, 1, 5, 3118120485922352640062234404786927487189778432000000⟩,
  ⟨4, 4, 6, 7, 2, 5, 2895635507067241820372505611332664020420263936000000⟩,
  ⟨4, 4, 7, 7, 3, 5, -2277252336920720740302258506670059688770823782400000⟩,
  ⟨4, 4, 8, 7, 4, 5, -202046160668745132568331960629825567815892992000000⟩
]

def collectedFourData_10_3_35 : List CollectedFourTerm := [
  ⟨4, 5, 1, 0, 4, 6, -417949487709421813544999555483580728120180736000000⟩,
  ⟨4, 5, 2, 0, 5, 6, 10293318978328948201547875646781503596998426624000000⟩,
  ⟨4, 5, 3, 0, 6, 6, 826092601979934142129965758808693004080827596800000⟩,
  ⟨4, 5, 4, 0, 7, 6, -3950356505163494900299491581811597621260294553600000⟩,
  ⟨4, 5, 5, 0, 8, 6, -93097600219846272399848925211507179720278016000000⟩,
  ⟨4, 5, 1, 1, 3, 6, 1687968609217236838968057190832093699252001177600000⟩,
  ⟨4, 5, 2, 1, 4, 6, -35476382267659834298356719470542750503893414707200000⟩,
  ⟨4, 5, 3, 1, 5, 6, -11074950871153467290620004403282350466828494438400000⟩,
  ⟨4, 5, 4, 1, 6, 6, -8850909382929606797327294794993347866472638054400000⟩,
  ⟨4, 5, 5, 1, 7, 6, 738407014547530661252621829491708583072497664000000⟩,
  ⟨4, 5, 6, 1, 8, 6, 80780019009399774709202815056875116356540825600000⟩,
  ⟨4, 5, 1, 2, 2, 6, 294682671407237429230104672455708167161407078400000⟩,
  ⟨4, 5, 2, 2, 3, 6, 13221829817587894427759696643123086525217531494400000⟩,
  ⟨4, 5, 3, 2, 4, 6, 14421966093301256964552447521748140828436253900800000⟩,
  ⟨4, 5, 4, 2, 5, 6, 1123134015514208328620800426684730778022261555200000⟩,
  ⟨4, 5, 5, 2, 6, 6, 516108108993115902667151708065661657926336512000000⟩,
  ⟨4, 5, 6, 2, 7, 6, 108092904912390627816718495164584196621887078400000⟩,
  ⟨4, 5, 7, 2, 8, 6, 84489139495149576149927167037420436434033049600000⟩,
  ⟨4, 5, 1, 3, 1, 6, -1653765094899193611926588776810803990217359360000000⟩,
  ⟨4, 5, 2, 3, 2, 6, 7070098329528024203810142308457221773162708992000000⟩,
  ⟨4, 5, 3, 3, 3, 6, -19277002470163739344036447827896943454296893030400000⟩,
  ⟨4, 5, 4, 3, 4, 6, -770582120794453729729332752159892850915619635200000⟩,
  ⟨4, 5, 5, 3, 5, 6, -195016486297101942948304913728956231214694400000000⟩,
  ⟨4, 5, 6, 3, 6, 6, -286414592895413640298386808443532506339842457600000⟩,
  ⟨4, 5, 7, 3, 7, 6, -47176971007096980891214494586964712473650790400000⟩,
  ⟨4, 5, 8, 3, 8, 6, -30497533339039826965647746229517977177292800000000⟩,
  ⟨4, 5, 1, 4, 0, 6, 13232607037274528867168128877485895670318288076800000⟩,
  ⟨4, 5, 2, 4, 1, 6, 16320878868537470707380847724883507747053214105600000⟩,
  ⟨4, 5, 3, 4, 2, 6, 26389341934165554061609031135371196486972866560000000⟩,
  ⟨4, 5, 4, 4, 3, 6, -1722363249402365964242277839707172204061917184000000⟩,
  ⟨4, 5, 5, 4, 4, 6, 702567919073158529341049645829181005769998336000000⟩,
  ⟨4, 5, 6, 4, 5, 6, 227871809951652311043506015723880027250910822400000⟩,
  ⟨4, 5, 7, 4, 6, 6, 15494112783886082872597816032138364339617792000000⟩,
  ⟨4, 5, 8, 4, 7, 6, -10833530863515999866701078885938010670078361600000⟩,
  ⟨4, 5, 2, 5, 0, 6, -121771303811540282273741177559387164436012938035200000⟩,
  ⟨4, 5, 3, 5, 1, 6, -21914298379777206506300790791892756262603141939200000⟩,
  ⟨4, 5, 4, 5, 2, 6, 11801049955399177558449820311145887685149091430400000⟩,
  ⟨4, 5, 5, 5, 3, 6, -1832337522406604414455726961991126100582858752000000⟩,
  ⟨4, 5, 6, 5, 4, 6, 257012308664611453155960582534888468665440665600000⟩,
  ⟨4, 5, 7, 5, 5, 6, 41035257553026021229392409489607106405964185600000⟩,
  ⟨4, 5, 8, 5, 6, 6, -22558254591623670814129340911369872560514662400000⟩,
  ⟨4, 5, 3, 6, 0, 6, -11934538094222283178419877158795079594097718067200000⟩,
  ⟨4, 5, 4, 6, 1, 6, -6332515504538882996188378214688556734100380057600000⟩,
  ⟨4, 5, 5, 6, 2, 6, -27118457178230748680371261274983398541099008000000⟩,
  ⟨4, 5, 6, 6, 3, 6, -951662423412671226597163586453462701500373401600000⟩,
  ⟨4, 5, 7, 6, 4, 6, -14690030479771616786561212678410306816521011200000⟩,
  ⟨4, 5, 8, 6, 5, 6, 23673881822418431825527057918735390396435660800000⟩,
  ⟨4, 5, 4, 7, 0, 6, -120832200730974731941505300121256898916420629299200000⟩,
  ⟨4, 5, 5, 7, 1, 6, 1264169163373911986690111136208266014842945536000000⟩,
  ⟨4, 5, 6, 7, 2, 6, 939174257808623756691429937921696718423221862400000⟩,
  ⟨4, 5, 7, 7, 3, 6, -615505867408195696763516643015714040988880076800000⟩,
  ⟨4, 5, 8, 7, 4, 6, -46808513938112508663761949422368979473661952000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1012
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1012. -/
namespace LaughlinFock
def collectedFourData_10_3_36 : List CollectedFourTerm := [
  ⟨4, 6, 0, 0, 3, 7, 6160813201129171472566306472872648288977813504000000⟩,
  ⟨4, 6, 1, 0, 4, 7, -170510512078992745801025028747636566686433280000000⟩,
  ⟨4, 6, 2, 0, 5, 7, 2099678479816112277877140326637007282120949760000000⟩,
  ⟨4, 6, 3, 0, 6, 7, 112340108657816932443128095668669496833343488000000⟩,
  ⟨4, 6, 4, 0, 7, 7, -402905931456907518627050237832186648625938432000000⟩,
  ⟨4, 6, 5, 0, 8, 7, -7596190426651639648740435833172561059905536000000⟩,
  ⟨4, 6, 0, 1, 2, 7, -2409816446790848621856663760226268714218029056000000⟩,
  ⟨4, 6, 1, 1, 3, 7, 688639178643998653631431478522883081920053248000000⟩,
  ⟨4, 6, 2, 1, 4, 7, -7236635389028629470670917180043617296845897728000000⟩,
  ⟨4, 6, 3, 1, 5, 7, -1506079562101665676770383614911331790323974144000000⟩,
  ⟨4, 6, 4, 1, 6, 7, -902724572961635753387291133496108470163734528000000⟩,
  ⟨4, 6, 5, 1, 7, 7, 60249461657795161840605486309564046318239744000000⟩,
  ⟨4, 6, 6, 1, 8, 7, 5492626426593344880170516302031898487554048000000⟩,
  ⟨4, 6, 0, 2, 1, 7, -2489609580883685311895392364986669583208284160000000⟩,
  ⟨4, 6, 1, 2, 2, 7, 120221449433591215853893526368210434373189632000000⟩,
  ⟨4, 6, 2, 2, 3, 7, 2697049570719434248669504174511488415255494656000000⟩,
  ⟨4, 6, 3, 2, 4, 7, 1961239253441672544280336951768072789193392128000000⟩,
  ⟨4, 6, 4, 2, 5, 7, 114551017377850665485633781406810693775130624000000⟩,
  ⟨4, 6, 5, 2, 6, 7, 42111240970688703823377004765862259591217152000000⟩,
  ⟨4, 6, 6, 2, 7, 7, 7349762395821573627092989463219526300598272000000⟩,
  ⟨4, 6, 7, 2, 8, 7, 4924137917576480754945917654818021435244544000000⟩,
  ⟨4, 6, 0, 3, 0, 7, 13911325910197379447092549885199051162117996544000000⟩,
  ⟨4, 6, 1, 3, 1, 7, -674685198766589560694327469600862144089292800000000⟩,
  ⟨4, 6, 2, 3, 2, 7, 1442191128434631759516320380441974645278638080000000⟩,
  ⟨4, 6, 3, 3, 3, 7, -2621474332181226843348621441828296547436068864000000⟩,
  ⟨4, 6, 4, 3, 4, 7, -78593440044439477160384346853860892395700224000000⟩,
  ⟨4, 6, 5, 3, 5, 7, -15912143414556992120280123605060138985062400000000⟩,
  ⟨4, 6, 6, 3, 6, 7, -19474721362918538727608628910183762895044608000000⟩,
  ⟨4, 6, 7, 3, 7, 7, -2749535776557281062995423754349369471533056000000⟩,
  ⟨4, 6, 8, 3, 8, 7, -1555256729492997914121486802721144045568000000000⟩,
  ⟨4, 6, 1, 4, 0, 7, 5398495914976328714245127399174677937063460864000000⟩,
  ⟨4, 6, 2, 4, 1, 7, 3329207829282382329346864397183010707387449344000000⟩,
  ⟨4, 6, 3, 4, 2, 7, 3588679444879538002651975076201916981156249600000000⟩,
  ⟨4, 6, 4, 4, 3, 7, -175667782996432466091505712137075117082542080000000⟩,
  ⟨4, 6, 5, 4, 4, 7, 57325212339881548812311739633134816257376256000000⟩,
  ⟨4, 6, 6, 4, 5, 7, 15494112783886082872597816032138364339617792000000⟩,
  ⟨4, 6, 7, 4, 6, 7, 903017224630627956624058218142705259642880000000⟩,
  ⟨4, 6, 8, 4, 7, 7, -552468345303358645910331455506202750877696000000⟩,
  ⟨4, 6, 2, 5, 0, 7, -24839469816347700455181081063250956202643816448000000⟩,
  ⟨4, 6, 3, 5, 1, 7, -2980119486899595289856420120060335027516342272000000⟩,
  ⟨4, 6, 4, 5, 2, 7, 1203616184573401547980325670419790223688859648000000⟩,
  ⟨4, 6, 5, 5, 3, 7, -149507449313741463626317727350992400067592192000000⟩,
  ⟨4, 6, 6, 5, 4, 7, 17475517038028236326972652994535190322741248000000⟩,
  ⟨4, 6, 7, 5, 5, 7, 2391588657214011797804867365166474103619584000000⟩,
  ⟨4, 6, 8, 5, 6, 7, -1150384093992553737313067764594915613343744000000⟩,
  ⟨4, 6, 3, 6, 0, 7, -1622974595187517591509601414854473683411402752000000⟩,
  ⟨4, 6, 4, 6, 1, 7, -645867798130779397558066258735801154679078912000000⟩,
  ⟨4, 6, 5, 6, 2, 7, -2212698977378420373189532110114706862112768000000⟩,
  ⟨4, 6, 6, 6, 3, 7, -64708157291025903431103257105079302910640128000000⟩,
  ⟨4, 6, 7, 6, 4, 7, -856154252819089849855460361961643094048768000000⟩,
  ⟨4, 6, 8, 6, 5, 7, 1207276785575518879731099640927088592027648000000⟩,
  ⟨4, 6, 4, 7, 0, 7, -12323953628455235421042864825954096290834939904000000⟩,
  ⟨4, 6, 5, 7, 1, 7, 103148412781987170313205906012044444047507456000000⟩,
  ⟨4, 6, 6, 7, 2, 7, 63859026166056948749212487049676738623700992000000⟩,
  ⟨4, 6, 7, 7, 3, 7, -35872489627728958150395316683897960558231552000000⟩,
  ⟨4, 6, 8, 7, 4, 7, -2387053913197173119050667786089144642437120000000⟩
]

def collectedFourData_10_3_37 : List CollectedFourTerm := [
  ⟨4, 7, 0, 0, 3, 8, -30153615520174904903311449035998227125391222374400000⟩,
  ⟨4, 7, 1, 0, 4, 8, 417275143355729067893614642962564880483221504000000⟩,
  ⟨4, 7, 2, 0, 5, 8, -3425570376800052139735035953524859023248064512000000⟩,
  ⟨4, 7, 3, 0, 6, 8, -137459955908970767688109894405636462140928819200000⟩,
  ⟨4, 7, 4, 0, 7, 8, 394398276699018128758494783563476226297340887040000⟩,
  ⟨4, 7, 5, 0, 8, 8, 6196492737390184597807748968978247310743961600000⟩,
  ⟨4, 7, 0, 1, 2, 8, 11794657010117931458477368938219558803101817241600000⟩,
  ⟨4, 7, 1, 1, 3, 8, -1685245141108507822531904344383578206399522406400000⟩,
  ⟨4, 7, 2, 1, 4, 8, 11806380860049793262135533939487647402131298713600000⟩,
  ⟨4, 7, 3, 1, 5, 8, 1842846982038160551086578564404938985963100569600000⟩,
  ⟨4, 7, 4, 1, 6, 8, 883662880371383719041211707812987526396940124160000⟩,
  ⟨4, 7, 5, 1, 7, 8, -49147708341319235424890991333915728833570406400000⟩,
  ⟨4, 7, 6, 1, 8, 8, -3840461131543296407290207031871513024685670400000⟩,
  ⟨4, 7, 0, 2, 1, 8, 12185198227329998486681287515867601262792933376000000⟩,
  ⟨4, 7, 1, 2, 2, 8, -294207213005114148956792826295610130256468377600000⟩,
  ⟨4, 7, 2, 2, 3, 8, -4400165645850181637012475369923791831671452467200000⟩,
  ⟨4, 7, 3, 2, 4, 8, -2399782807102315480991339954655052682132402995200000⟩,
  ⟨4, 7, 4, 2, 5, 8, -112132188485231161486242780152257457826331361280000⟩,
  ⟨4, 7, 5, 2, 6, 8, -34351692648703435205271221131698983645950771200000⟩,
  ⟨4, 7, 6, 2, 7, 8, -5138976259257087253696983086424884034247065600000⟩,
  ⟨4, 7, 7, 2, 8, 8, -3012600704800260064550725107746210635893964800000⟩,
  ⟨4, 7, 0, 3, 0, 8, -68087890214729458606980160945652105796531938918400000⟩,
  ⟨4, 7, 1, 3, 1, 8, 1651096812757752722112721841553545127568343040000000⟩,
  ⟨4, 7, 2, 3, 2, 8, -2352897005298726868302692394475380477416964096000000⟩,
  ⟨4, 7, 3, 3, 3, 8, 3207649969573498777416222428370710800994245017600000⟩,
  ⟨4, 7, 4, 3, 4, 8, 76933881815263879876702618128961357372226273280000⟩,
  ⟨4, 7, 5, 3, 5, 8, 12980122346416160349417186815754439690813440000000⟩,
  ⟨4, 7, 6, 3, 6, 8, 13616784509466854005023000452591433682413158400000⟩,
  ⟨4, 7, 7, 3, 7, 8, 1682173317843781011326551317151878338523955200000⟩,
  ⟨4, 7, 8, 3, 8, 8, 845786856112169307532632218097541133107200000000⟩,
  ⟨4, 7, 1, 4, 0, 8, -13211256768635307822410252401584094821792035635200000⟩,
  ⟨4, 7, 2, 4, 1, 8, -5431515266660885653130238005369588287089200332800000⟩,
  ⟨4, 7, 3, 4, 2, 8, -4391127302245544328064839759130401746599280640000000⟩,
  ⟨4, 7, 4, 4, 3, 8, 171958428695260246164209357916121838562941337600000⟩,
  ⟨4, 7, 5, 4, 4, 8, -46762290303720467203183100851196436491639193600000⟩,
  ⟨4, 7, 6, 4, 5, 8, -10833530863515999866701078885938010670078361600000⟩,
  ⟨4, 7, 7, 4, 6, 8, -552468345303358645910331455506202750877696000000⟩,
  ⟨4, 7, 8, 4, 7, 8, 300445872385292138285250233474630191310438400000⟩,
  ⟨4, 7, 2, 5, 0, 8, 40524943602675660008524841794935007801620666777600000⟩,
  ⟨4, 7, 3, 5, 1, 8, 3646490093048157196698629202212567461453941964800000⟩,
  ⟨4, 7, 4, 5, 2, 8, -1178200944538758921992287018654314477616952770560000⟩,
  ⟨4, 7, 5, 5, 3, 8, 121958741398573907503326688730137883107865395200000⟩,
  ⟨4, 7, 6, 5, 4, 8, -12218934754642647844755394059821891767920230400000⟩,
  ⟨4, 7, 7, 5, 5, 8, -1463180316009768704603242394433708278729932800000⟩,
  ⟨4, 7, 8, 5, 6, 8, 625607160366759792358686302529680695728537600000⟩,
  ⟨4, 7, 3, 6, 0, 8, 1985880367762421206645167505201257540890709196800000⟩,
  ⟨4, 7, 4, 6, 1, 8, 632229825053873818602553772899146597279612272640000⟩,
  ⟨4, 7, 5, 6, 2, 8, 1804980177333415568960722777270347493067980800000⟩,
  ⟨4, 7, 6, 6, 3, 8, 45244140720508845937971912966693215560689254400000⟩,
  ⟨4, 7, 7, 6, 4, 8, 523797454221177325340951209736636376652185600000⟩,
  ⟨4, 7, 8, 6, 5, 8, -656546805145150707420569799456068834898739200000⟩,
  ⟨4, 7, 4, 7, 0, 8, 12063724293175892874376222591502345118403138682880000⟩,
  ⟨4, 7, 5, 7, 1, 8, -84141965219090223287816221824146217939605913600000⟩,
  ⟨4, 7, 6, 7, 2, 8, -44650425650931560593898135473498348324493721600000⟩,
  ⟨4, 7, 7, 7, 3, 8, 21946884783565318120111511628177513673811558400000⟩,
  ⟨4, 7, 8, 7, 4, 8, 1298138620027991862828725028268185955074048000000⟩
]

def collectedFourData_10_3_38 : List CollectedFourTerm := [
  ⟨5, 0, 5, 0, 8, 2, 9949994396324421157848572371667337577668123033600000⟩,
  ⟨5, 0, 5, 1, 7, 2, -78918743765731702797385195514916111717409121894400000⟩,
  ⟨5, 0, 6, 1, 8, 2, -43167639905886888204242116413862500805963992268800000⟩,
  ⟨5, 0, 5, 2, 6, 2, -55160098437041930165963716223779713435550561075200000⟩,
  ⟨5, 0, 6, 2, 7, 2, -57763239633508740293677910190834451630819324723200000⟩,
  ⟨5, 0, 7, 2, 8, 2, -135449216071382656397563006125559205418796213862400000⟩,
  ⟨5, 0, 5, 3, 5, 2, 20842781567568173224511360896549310410512138240000000⟩,
  ⟨5, 0, 6, 3, 6, 2, 153055695721756589542803891214884193787177651404800000⟩,
  ⟨5, 0, 7, 3, 7, 2, 75632013507493248065393733196401394157016947097600000⟩,
  ⟨5, 0, 8, 3, 8, 2, 114081995441345649656993879681903357078588620800000000⟩,
  ⟨5, 0, 5, 4, 4, 2, -75088367920411900960336994642294243489675319705600000⟩,
  ⟨5, 0, 6, 4, 5, 2, -121771303811540282273741177559387164436012938035200000⟩,
  ⟨5, 0, 7, 4, 6, 2, -24839469816347700455181081063250956202643816448000000⟩,
  ⟨5, 0, 8, 4, 7, 2, 40524943602675660008524841794935007801620666777600000⟩,
  ⟨5, 0, 5, 5, 3, 2, 195834780242102277344873661316335111094024745779200000⟩,
  ⟨5, 0, 6, 5, 4, 2, -137343552624363722408191064974040964070510480588800000⟩,
  ⟨5, 0, 7, 5, 5, 2, -65785892720137694812974219435266734020117292646400000⟩,
  ⟨5, 0, 8, 5, 6, 2, 84383568627565241992969800163009967525835728486400000⟩,
  ⟨5, 0, 5, 6, 2, 2, 2898339982160340144278816847836017119416077516800000⟩,
  ⟨5, 0, 6, 6, 3, 2, 508554235436136201715124797294486999273315290316800000⟩,
  ⟨5, 0, 7, 6, 4, 2, 23550400967973075137464922172985219686798773452800000⟩,
  ⟨5, 0, 8, 6, 5, 2, -88556790745002757089465865115293999934691134668800000⟩,
  ⟨5, 0, 5, 7, 1, 2, -135110637243849314957996640724531557201929148825600000⟩,
  ⟨5, 0, 6, 7, 2, 2, -501880745599275996257717741215428362945812443955200000⟩,
  ⟨5, 0, 7, 7, 3, 2, 986751524822461543417303677944130608499449344819200000⟩,
  ⟨5, 0, 8, 7, 4, 2, 175096412366838267382247450062067432596514537472000000⟩
]

def collectedFourData_10_3_39 : List CollectedFourTerm := [
  ⟨5, 1, 4, 0, 7, 3, 37990346931906223490198113172669181284582298746880000⟩,
  ⟨5, 1, 5, 0, 8, 3, 3581256654944351350102700642664784227541922611200000⟩,
  ⟨5, 1, 4, 1, 6, 3, 85118676676611323670251427454557148720215380459520000⟩,
  ⟨5, 1, 5, 1, 7, 3, -28404867887692382165317862097006626143946460364800000⟩,
  ⟨5, 1, 6, 1, 8, 3, -7768567073178791573726318176406281046494858444800000⟩,
  ⟨5, 1, 4, 2, 5, 3, -10801113986709357548789860969080095219017486172160000⟩,
  ⟨5, 1, 5, 2, 6, 3, -19853525715352676477500216674356886459675731558400000⟩,
  ⟨5, 1, 6, 2, 7, 3, -10395231299078192210963753969613721431071470387200000⟩,
  ⟨5, 1, 7, 2, 8, 3, -16250542031856988538227682110918247378901899673600000⟩,
  ⟨5, 1, 4, 3, 4, 3, 7410643082526994307340877828301344111081983836160000⟩,
  ⟨5, 1, 5, 3, 5, 3, 7501848465761811420709432496133830449645486080000000⟩,
  ⟨5, 1, 6, 3, 6, 3, 27544323496461522485590496525462864476966276300800000⟩,
  ⟨5, 1, 7, 3, 7, 3, 9073963291229171278868689583011918445948593766400000⟩,
  ⟨5, 1, 8, 3, 8, 3, 10265254660207981431600962753164918535906918400000000⟩,
  ⟨5, 1, 4, 4, 3, 3, 16563866400927047404107438891115983876146803507200000⟩,
  ⟨5, 1, 5, 4, 4, 3, -27026217966838459657819441893835322629811286835200000⟩,
  ⟨5, 1, 6, 4, 5, 3, -21914298379777206506300790791892756262603141939200000⟩,
  ⟨5, 1, 7, 4, 6, 3, -2980119486899595289856420120060335027516342272000000⟩,
  ⟨5, 1, 8, 4, 7, 3, 3646490093048157196698629202212567461453941964800000⟩,
  ⟨5, 1, 4, 5, 2, 3, -113490005618572945370803947605752554356532911800320000⟩,
  ⟨5, 1, 5, 5, 3, 3, 70485930149937566229891661637834119313617217126400000⟩,
  ⟨5, 1, 6, 5, 4, 3, -24716723058225984598520269840796116923192233164800000⟩,
  ⟨5, 1, 7, 5, 5, 3, -7892673326277741597234696665631139444377098649600000⟩,
  ⟨5, 1, 8, 5, 6, 3, 7592949419827194692052782109818050792461120307200000⟩,
  ⟨5, 1, 4, 6, 1, 3, 60899430381701865717589951044582287202869921710080000⟩,
  ⟨5, 1, 5, 6, 2, 3, 1043186451766980367581445189728893243527633305600000⟩,
  ⟨5, 1, 6, 6, 3, 3, 91520817374961698631547308266390983129372085452800000⟩,
  ⟨5, 1, 7, 6, 4, 3, 2825463239266315831059672442808057560195871539200000⟩,
  ⟨5, 1, 8, 6, 5, 3, -7968461678561605586849952208291965113301624422400000⟩,
  ⟨5, 1, 4, 7, 0, 3, 1162036190990685244935085531298604335080318288527360000⟩,
  ⟨5, 1, 5, 7, 1, 3, -48629762943590201441262339078530176164859949875200000⟩,
  ⟨5, 1, 6, 7, 2, 3, -90319837809647184758065419112664615599335486259200000⟩,
  ⟨5, 1, 7, 7, 3, 3, 118385676892184461038503496621027887915790552268800000⟩,
  ⟨5, 1, 8, 7, 4, 3, 15755415708506857499618792986665884932380819456000000⟩
]

def collectedFourData_10_3_40 : List CollectedFourTerm := [
  ⟨5, 2, 3, 0, 6, 4, 4278177307592058975824838930031306611558218465280000⟩,
  ⟨5, 2, 4, 0, 7, 4, -61374447066043256532230714351577877876261445959680000⟩,
  ⟨5, 2, 5, 0, 8, 4, -2892809157452047389335518830595484796501727641600000⟩,
  ⟨5, 2, 3, 1, 5, 4, -57355075431139797979826419509962665073561976176640000⟩,
  ⟨5, 2, 4, 1, 6, 4, -137511555906136197677391643633510912041897657630720000⟩,
  ⟨5, 2, 5, 1, 7, 4, 22944421430473807573366222021063212819280193126400000⟩,
  ⟨5, 2, 6, 1, 8, 4, 4183444366945967531870883084392143706870356377600000⟩,
  ⟨5, 2, 3, 2, 4, 4, 74688634086959452338734783953110055079911285063680000⟩,
  ⟨5, 2, 4, 2, 5, 4, 17449495784278963740020234633540131248364333301760000⟩,
  ⟨5, 2, 5, 2, 6, 4, 16036957562868212667694378895853681213168628531200000⟩,
  ⟨5, 2, 6, 2, 7, 4, 5597927058050672417142601264018597796460783206400000⟩,
  ⟨5, 2, 7, 2, 8, 4, 6563299050127108904547467364847832059024402022400000⟩,
  ⟨5, 2, 3, 3, 3, 4, -99831949019504462618697693334020067925816078499840000⟩,
  ⟨5, 2, 4, 3, 4, 4, -11972097080585179790864888739655828664393410805760000⟩,
  ⟨5, 2, 5, 3, 5, 4, -6059720938908963887671546683023420164606525440000000⟩,
  ⟨5, 2, 6, 3, 6, 4, -14832869934333824439992631794140088273867479449600000⟩,
  ⟨5, 2, 7, 3, 7, 4, -3664809120425822878802474056244272816998422937600000⟩,
  ⟨5, 2, 8, 3, 8, 4, -3316760070086446996596671185475915364150804480000000⟩,
  ⟨5, 2, 3, 4, 2, 4, 136665409609583837927490470324984056025947570176000000⟩,
  ⟨5, 2, 4, 4, 3, 4, -26759380309289008651945735398651564876155269939200000⟩,
  ⟨5, 2, 5, 4, 4, 4, 21830798057387541287936926624149422678059096473600000⟩,
  ⟨5, 2, 6, 4, 5, 4, 11801049955399177558449820311145887685149091430400000⟩,
  ⟨5, 2, 7, 4, 6, 4, 1203616184573401547980325670419790223688859648000000⟩,
  ⟨5, 2, 8, 4, 7, 4, -1178200944538758921992287018654314477616952770560000⟩,
  ⟨5, 2, 3, 5, 1, 4, -113490005618572945370803947605752554356532911800320000⟩,
  ⟨5, 2, 4, 5, 2, 4, 183346215680704186268312459908465959248105853419520000⟩,
  ⟨5, 2, 5, 5, 3, 4, -56935976350020399610748584964892991561416258355200000⟩,
  ⟨5, 2, 6, 5, 4, 4, 13310181256501491556006049299382161315565509017600000⟩,
  ⟨5, 2, 7, 5, 5, 4, 3187707538848335519727080370634894094134306406400000⟩,
  ⟨5, 2, 8, 5, 6, 4, -2453323593372855259904580616754840076518518947840000⟩,
  ⟨5, 2, 3, 6, 0, 4, -61806715044925380978241347701035143126303501189120000⟩,
  ⟨5, 2, 4, 6, 1, 4, -98384699487302218364132876232929500348409582714880000⟩,
  ⟨5, 2, 5, 6, 2, 4, -842648157158767383002492439726671241109359820800000⟩,
  ⟨5, 2, 6, 6, 3, 4, -49284796578181316166122306588389766267145918873600000⟩,
  ⟨5, 2, 7, 6, 4, 4, -1141153332491431134705312836921142105302944972800000⟩,
  ⟨5, 2, 8, 6, 5, 4, 2574653663285902141505498062578717071221488353280000⟩,
  ⟨5, 2, 4, 7, 0, 4, -1877301326587432336284891449426530543295672572968960000⟩,
  ⟨5, 2, 5, 7, 1, 4, 39281357669163178445202848775132835683052919193600000⟩,
  ⟨5, 2, 6, 7, 2, 4, 48638058106336421229459373844543047997157959270400000⟩,
  ⟨5, 2, 7, 7, 3, 4, -47813826712482855631170769196873754028234978099200000⟩,
  ⟨5, 2, 8, 7, 4, 4, -5090661210009333527610200988218493820126573363200000⟩
]

def collectedFourData_10_3_41 : List CollectedFourTerm := [
  ⟨5, 3, 2, 0, 5, 5, -16553898964592293689392062044660575509785083904000000⟩,
  ⟨5, 3, 3, 0, 6, 5, -2657073679998409891887023981594344178335717785600000⟩,
  ⟨5, 3, 4, 0, 7, 5, 19059101131017118790435059560012521394381049036800000⟩,
  ⟨5, 3, 5, 0, 8, 5, 598884877124650193157858386035570147426566144000000⟩,
  ⟨5, 3, 2, 1, 4, 5, 57053750002745403172777216090447331839968490291200000⟩,
  ⟨5, 3, 3, 1, 5, 5, 35621866600049908353589412681239013443515501772800000⟩,
  ⟨5, 3, 4, 1, 6, 5, 42702570466799437729788040611694437690326070067200000⟩,
  ⟨5, 3, 5, 1, 7, 5, -4750077264408437032952577494461035384171134976000000⟩,
  ⟨5, 3, 6, 1, 8, 5, -649559328655206111750590826625706379379212288000000⟩,
  ⟨5, 3, 2, 2, 3, 5, -21263582270032431104518061161144573891898140262400000⟩,
  ⟨5, 3, 3, 2, 4, 5, -46387325620029052371299989992103019006691744153600000⟩,
  ⟨5, 3, 4, 2, 5, 5, -5418732399820383068178332289997047415887731097600000⟩,
  ⟨5, 3, 5, 2, 6, 5, -3320057023032555361504951636869666269307076608000000⟩,
  ⟨5, 3, 6, 2, 7, 5, -869184677204809110866676046043572157527621632000000⟩,
  ⟨5, 3, 7, 2, 8, 5, -815261636262888555531472371125450366726543769600000⟩,
  ⟨5, 3, 2, 3, 2, 5, -11370258092957686164650676267472452345221087232000000⟩,
  ⟨5, 3, 3, 3, 3, 5, 62003237615219017222075292218029402739312479436800000⟩,
  ⟨5, 3, 4, 3, 4, 5, 3717791685580363373224750995259033773112138137600000⟩,
  ⟨5, 3, 5, 3, 5, 5, 1254515950545666803992145219911427848509849600000000⟩,
  ⟨5, 3, 6, 3, 6, 5, 2303085254988001026601789896789231019279515648000000⟩,
  ⟨5, 3, 7, 3, 7, 5, 455225071612674816731200994926311049150228070400000⟩,
  ⟨5, 3, 8, 3, 8, 5, 343326735175165940555739668921430826391961600000000⟩,
  ⟨5, 3, 2, 4, 1, 5, -26247528165786975470143282992494691984256637337600000⟩,
  ⟨5, 3, 3, 4, 2, 5, -84879619691174533648466819273173532027671019520000000⟩,
  ⟨5, 3, 4, 4, 3, 5, 8309805788869767370458142954158221989345492992000000⟩,
  ⟨5, 3, 5, 4, 4, 5, -4519528977033222425293915885091088077395329024000000⟩,
  ⟨5, 3, 6, 4, 5, 5, -1832337522406604414455726961991126100582858752000000⟩,
  ⟨5, 3, 7, 4, 6, 5, -149507449313741463626317727350992400067592192000000⟩,
  ⟨5, 3, 8, 4, 7, 5, 121958741398573907503326688730137883107865395200000⟩,
  ⟨5, 3, 2, 5, 0, 5, 195834780242102277344873661316335111094024745779200000⟩,
  ⟨5, 3, 3, 5, 1, 5, 70485930149937566229891661637834119313617217126400000⟩,
  ⟨5, 3, 4, 5, 2, 5, -56935976350020399610748584964892991561416258355200000⟩,
  ⟨5, 3, 5, 5, 3, 5, 11787191392323702922217099668582462915784736768000000⟩,
  ⟨5, 3, 6, 5, 4, 5, -2066658868363023046106036892022494226953535488000000⟩,
  ⟨5, 3, 7, 5, 5, 5, -395961793634667482080171353724385319542430105600000⟩,
  ⟨5, 3, 8, 5, 6, 5, 253950108492157391585702932672633361109142732800000⟩,
  ⟨5, 3, 3, 6, 0, 5, 38386673572785091995113715529041537041823065702400000⟩,
  ⟨5, 3, 4, 6, 1, 5, 30552192759560909007837583791726834796964138188800000⟩,
  ⟨5, 3, 5, 6, 2, 5, 174449543883437682409041581943017995681923072000000⟩,
  ⟨5, 3, 6, 6, 3, 5, 7652402319766604251315699413799400188850208768000000⟩,
  ⟨5, 3, 7, 6, 4, 5, 141748612392695216780870136297267681622700851200000⟩,
  ⟨5, 3, 8, 6, 5, 5, -266509309610595636158408647852038095726287257600000⟩,
  ⟨5, 3, 4, 7, 0, 5, 582973493811211058823911355727944491583195945369600000⟩,
  ⟨5, 3, 5, 7, 1, 5, -8132237482857936388047077168753249105240653824000000⟩,
  ⟨5, 3, 6, 7, 2, 5, -7551983867711570688691385308163685555426557952000000⟩,
  ⟨5, 3, 7, 7, 3, 5, 5939205010147154044424382213688130715020741836800000⟩,
  ⟨5, 3, 8, 7, 4, 5, 526948002322583190739794549121067971975839744000000⟩
]

def collectedFourData_10_3_42 : List CollectedFourTerm := [
  ⟨5, 4, 1, 0, 4, 6, -471397329771423334425634804481032524172099584000000⟩,
  ⟨5, 4, 2, 0, 5, 6, 11609639976980399229642424020811873833248096256000000⟩,
  ⟨5, 4, 3, 0, 6, 6, 931734236238638053754333562297394888944333619200000⟩,
  ⟨5, 4, 4, 0, 7, 6, -4455532457725905703099956697990030178436671078400000⟩,
  ⟨5, 4, 5, 0, 8, 6, -105003024150790669513970292302139473635835904000000⟩,
  ⟨5, 4, 1, 1, 3, 6, 1903827899117319789194362557810556414045087334400000⟩,
  ⟨5, 4, 2, 1, 4, 6, -40013141211341941107161113068353243152642788556800000⟩,
  ⟨5, 4, 3, 1, 5, 6, -12491227819475451746197282078507411008283842969600000⟩,
  ⟨5, 4, 4, 1, 6, 6, -9982773449557686915799326630938925884142885273600000⟩,
  ⟨5, 4, 5, 1, 7, 6, 832835319047449760747412840195293858041430016000000⟩,
  ⟨5, 4, 6, 1, 8, 6, 91110257051901268442055571492327914016761446400000⟩,
  ⟨5, 4, 1, 2, 2, 6, 332367016867502633191741336745158221034527129600000⟩,
  ⟨5, 4, 2, 2, 3, 6, 14912652016543228973338226748378061483816884633600000⟩,
  ⟨5, 4, 3, 2, 4, 6, 16266263044597484263456506179178449839540351795200000⟩,
  ⟨5, 4, 4, 2, 5, 6, 1266761633781323003154804871347271216145419468800000⟩,
  ⟨5, 4, 5, 2, 6, 6, 582108583948980961335885131442826354442108928000000⟩,
  ⟨5, 4, 6, 2, 7, 6, 121915944967884311133356668151726049391647129600000⟩,
  ⟨5, 4, 7, 2, 8, 6, 95293703961635392749686428611657519356864102400000⟩,
  ⟨5, 4, 1, 3, 1, 6, -1865250401614717268814035688118509377515683840000000⟩,
  ⟨5, 4, 2, 3, 2, 6, 7974230311960685188897994408664862904756994048000000⟩,
  ⟨5, 4, 3, 3, 3, 6, -21742166835122711889164746089258691176429099417600000⟩,
  ⟨5, 4, 4, 3, 4, 6, -869125013414670448121814709783575335564790988800000⟩,
  ⟨5, 4, 5, 3, 5, 6, -219955409936459758491498575472468755585433600000000⟩,
  ⟨5, 4, 6, 3, 6, 6, -323041607344512672493198201575175894518359654400000⟩,
  ⟨5, 4, 7, 3, 7, 6, -53210014160637140281702263333141347237992857600000⟩,
  ⟨5, 4, 8, 3, 8, 6, -34397591583204725679805130804039781659443200000000⟩,
  ⟨5, 4, 1, 4, 0, 6, 14924807438985501689059123737977830267524690739200000⟩,
  ⟨5, 4, 2, 4, 1, 6, 18408010882646132213762527110232514531045041766400000⟩,
  ⟨5, 4, 3, 4, 2, 6, 29764040124483825130433457825349495635459440640000000⟩,
  ⟨5, 4, 4, 4, 3, 6, -1942620963873966127271402947669084402819792896000000⟩,
  ⟨5, 4, 5, 4, 4, 6, 792413080463949100378534514248476347527593984000000⟩,
  ⟨5, 4, 6, 4, 5, 6, 257012308664611453155960582534888468665440665600000⟩,
  ⟨5, 4, 7, 4, 6, 6, 17475517038028236326972652994535190322741248000000⟩,
  ⟨5, 4, 8, 4, 7, 6, -12218934754642647844755394059821891767920230400000⟩,
  ⟨5, 4, 2, 5, 0, 6, -137343552624363722408191064974040964070510480588800000⟩,
  ⟨5, 4, 3, 5, 1, 6, -24716723058225984598520269840796116923192233164800000⟩,
  ⟨5, 4, 4, 5, 2, 6, 13310181256501491556006049299382161315565509017600000⟩,
  ⟨5, 4, 5, 5, 3, 6, -2066658868363023046106036892022494226953535488000000⟩,
  ⟨5, 4, 6, 5, 4, 6, 289879326535074728873390509601767898508322406400000⟩,
  ⟨5, 4, 7, 5, 5, 6, 46282891607293693329619987640716802556061286400000⟩,
  ⟨5, 4, 8, 5, 6, 6, -25443029101613679749542480470579817328777625600000⟩,
  ⟨5, 4, 3, 6, 0, 6, -13460740005938500427906629033080480318972808396800000⟩,
  ⟨5, 4, 4, 6, 1, 6, -7142324580742567557841538967281848504889534054400000⟩,
  ⟨5, 4, 5, 6, 2, 6, -30586395431178041900350574556456334972157952000000⟩,
  ⟨5, 4, 6, 6, 3, 6, -1073362065112591986665266355381908309079909990400000⟩,
  ⟨5, 4, 7, 6, 4, 6, -16568607800853764858715193212687113752726732800000⟩,
  ⟨5, 4, 8, 6, 5, 6, 26701323974755313574405725537854165504701235200000⟩,
  ⟨5, 4, 4, 7, 0, 6, -136284356004731788085442876759568603323139149004800000⟩,
  ⟨5, 4, 5, 7, 1, 6, 1425832512105271811341224945323333530926710784000000⟩,
  ⟨5, 4, 6, 7, 2, 6, 1059276899099458473148631804347396857429334425600000⟩,
  ⟨5, 4, 7, 7, 3, 6, -694217437482760205576246052184834567149138739200000⟩,
  ⟨5, 4, 8, 7, 4, 6, -52794438394755492440973134229034653909516288000000⟩
]

def collectedFourData_10_3_43 : List CollectedFourTerm := [
  ⟨5, 5, 0, 0, 3, 7, 16316555840960566800422264219249342846847890227200000⟩,
  ⟨5, 5, 1, 0, 4, 7, -451587185162138497882361548596735511105634304000000⟩,
  ⟨5, 5, 2, 0, 5, 7, 5560876469636119998085003159978540844992954368000000⟩,
  ⟨5, 5, 3, 0, 6, 7, 297526251203151144761237188660709561716860518400000⟩,
  ⟨5, 5, 4, 0, 7, 7, -1067072952003471523255303939899378199290288537600000⟩,
  ⟨5, 5, 5, 0, 8, 7, -20118069032236653637775778725874094922583244800000⟩,
  ⟨5, 5, 0, 1, 2, 7, -6382258857210829794565761012587973176009215180800000⟩,
  ⟨5, 5, 1, 1, 3, 7, 1823820857051568608261566743734723670972982886400000⟩,
  ⟨5, 5, 2, 1, 4, 7, -19165808404013214313956171739210396145990133350400000⟩,
  ⟨5, 5, 3, 1, 5, 7, -3988764222141529470127315022839613625403126579200000⟩,
  ⟨5, 5, 4, 1, 6, 7, -2390813586270749566754538784465860643688703590400000⟩,
  ⟨5, 5, 5, 1, 7, 7, 159567198912482630230791615947349436681892659200000⟩,
  ⟨5, 5, 6, 1, 8, 7, 14546901987974584355706303397524573463668326400000⟩,
  ⟨5, 5, 0, 2, 1, 7, -6593586337146822541564786458486382053229068288000000⟩,
  ⟨5, 5, 1, 2, 2, 7, 318399524368776595667954304575450848719116697600000⟩,
  ⟨5, 5, 2, 2, 3, 7, 7142979098671053026083289989285394524301741260800000⟩,
  ⟨5, 5, 3, 2, 4, 7, 5194228221430198408977601185192740317131335270400000⟩,
  ⟨5, 5, 4, 2, 5, 7, 303381714501906126533986356911037536747598643200000⟩,
  ⟨5, 5, 5, 2, 6, 7, 111529175191426537036923815434156856011495833600000⟩,
  ⟨5, 5, 6, 2, 7, 7, 19465418709211152677629085335490468647639449600000⟩,
  ⟨5, 5, 7, 2, 8, 7, 13041293199086457103958841041560361667605299200000⟩,
  ⟨5, 5, 0, 3, 0, 7, 36843338472579346868040453063706692947289518899200000⟩,
  ⟨5, 5, 1, 3, 1, 7, -1786864552024879023862479621839385424602071040000000⟩,
  ⟨5, 5, 2, 3, 2, 7, 3819559417274437777153353955572035157642706944000000⟩,
  ⟨5, 5, 3, 3, 3, 7, -6942822470066153105983815237069296225836282675200000⟩,
  ⟨5, 5, 4, 3, 4, 7, -208150159946944315273717238819052543523631923200000⟩,
  ⟨5, 5, 5, 3, 5, 7, -42142387392204348259002028074357143969464320000000⟩,
  ⟨5, 5, 6, 3, 6, 7, -51577668114814450444980421638427841820780134400000⟩,
  ⟨5, 5, 7, 3, 7, 7, -7281985765563082097078647738070054491442380800000⟩,
  ⟨5, 5, 8, 3, 8, 7, -4119007092951810003035247254870512002662400000000⟩,
  ⟨5, 5, 1, 4, 0, 7, 14297602796618526023202848904040620552025748275200000⟩,
  ⟨5, 5, 2, 4, 1, 7, 8817213520236737407158303329996082794252677939200000⟩,
  ⟨5, 5, 3, 4, 2, 7, 9504409019730097107489151822276002820946657280000000⟩,
  ⟨5, 5, 4, 4, 3, 7, -465245917567130760623674775917840584507654144000000⟩,
  ⟨5, 5, 5, 4, 4, 7, 151822494482898039550797154094275959225896140800000⟩,
  ⟨5, 5, 6, 4, 5, 7, 41035257553026021229392409489607106405964185600000⟩,
  ⟨5, 5, 7, 4, 6, 7, 2391588657214011797804867365166474103619584000000⟩,
  ⟨5, 5, 8, 4, 7, 7, -1463180316009768704603242394433708278729932800000⟩,
  ⟨5, 5, 2, 5, 0, 7, -65785892720137694812974219435266734020117292646400000⟩,
  ⟨5, 5, 3, 5, 1, 7, -7892673326277741597234696665631139444377098649600000⟩,
  ⟨5, 5, 4, 5, 2, 7, 3187707538848335519727080370634894094134306406400000⟩,
  ⟨5, 5, 5, 5, 3, 7, -395961793634667482080171353724385319542430105600000⟩,
  ⟨5, 5, 6, 5, 4, 7, 46282891607293693329619987640716802556061286400000⟩,
  ⟨5, 5, 7, 5, 5, 7, 6333983615488969765773065870868151304139571200000⟩,
  ⟨5, 5, 8, 5, 6, 7, -3046725439547827373894895362777418006999859200000⟩,
  ⟨5, 5, 3, 6, 0, 7, -4298353926066760624166732687081525234938517913600000⟩,
  ⟨5, 5, 4, 6, 1, 7, -1710543340633605330622955107978321710894651801600000⟩,
  ⟨5, 5, 5, 6, 2, 7, -5860204691324541709249638439060460055979622400000⟩,
  ⟨5, 5, 6, 6, 3, 7, -171375795262088312096849672432751621429421670400000⟩,
  ⟨5, 5, 7, 6, 4, 7, -2267474798949947459323207602736267098744422400000⟩,
  ⟨5, 5, 8, 6, 5, 7, 3197402427934012790602667641467068928648806400000⟩,
  ⟨5, 5, 4, 7, 0, 7, -32639275205299700361985365239988049336081789747200000⟩,
  ⟨5, 5, 5, 7, 1, 7, 273182578682189938296394631359513712594308300800000⟩,
  ⟨5, 5, 6, 7, 2, 7, 169126920809229678171088144304932888432449945600000⟩,
  ⟨5, 5, 7, 7, 3, 7, -95006204709767857359442781872901698757433753600000⟩,
  ⟨5, 5, 8, 7, 4, 7, -6321973609413530119190375564745907598524416000000⟩
]

def collectedFourData_10_3_44 : List CollectedFourTerm := [
  ⟨5, 6, 0, 0, 3, 8, -62787741534275616650945660052133779629588191641600000⟩,
  ⟨5, 6, 1, 0, 4, 8, 868876365163170037459279865098099218035245056000000⟩,
  ⟨5, 6, 2, 0, 5, 8, -7132936588718075635855389778743825341683335168000000⟩,
  ⟨5, 6, 3, 0, 6, 8, -286227705501874629496950888382010375231294668800000⟩,
  ⟨5, 6, 4, 0, 7, 8, 821240724594807352067097882161317921115665858560000⟩,
  ⟨5, 6, 5, 0, 8, 8, 12902724190867250106946092097567103891433062400000⟩,
  ⟨5, 6, 0, 1, 2, 8, 24559571482936422267620414842482468066324538982400000⟩,
  ⟨5, 6, 1, 1, 3, 8, -3509122687825564815284975885745834096873544089600000⟩,
  ⟨5, 6, 2, 1, 4, 8, 24583983615498630646075752715359141414998271590400000⟩,
  ⟨5, 6, 3, 1, 5, 8, 3837291084315076638402855068461507126854313574400000⟩,
  ⟨5, 6, 4, 1, 6, 8, 1840018040260205815190589058377687496749471498240000⟩,
  ⟨5, 6, 5, 1, 7, 8, -102338427916614041922871862858734588678216089600000⟩,
  ⟨5, 6, 6, 1, 8, 8, -7996848030991060287114598481901841039333785600000⟩,
  ⟨5, 6, 0, 2, 1, 8, 25372780797367928357162235300478567070526603264000000⟩,
  ⟨5, 6, 1, 2, 2, 8, -612616634158686432652156444182521933994550886400000⟩,
  ⟨5, 6, 2, 2, 3, 8, -9162299728030677366763943018378474245461953740800000⟩,
  ⟨5, 6, 3, 2, 4, 8, -4996977643690025670330712697494398813206269132800000⟩,
  ⟨5, 6, 4, 2, 5, 8, -233488646280999351708661521702402391512365137920000⟩,
  ⟨5, 6, 5, 2, 6, 8, -71529239929738158098488073635890233539873996800000⟩,
  ⟨5, 6, 6, 2, 7, 8, -10700697331009178840144358026737997828220518400000⟩,
  ⟨5, 6, 7, 2, 8, 8, -6273025344918177230060519243740279280448307200000⟩,
  ⟨5, 6, 0, 3, 0, 8, -141776857556475525939154281259800021259609807257600000⟩,
  ⟨5, 6, 1, 3, 1, 8, 3438016905738496841792208796492960671266242560000000⟩,
  ⟨5, 6, 2, 3, 2, 8, -4899349098837706095366767860241859533648953344000000⟩,
  ⟨5, 6, 3, 3, 3, 8, 6679169106180858664996906006375025995642463846400000⟩,
  ⟨5, 6, 4, 3, 4, 8, 160196533759387681059965476394832572859725905920000⟩,
  ⟨5, 6, 5, 3, 5, 8, 27028021446541469054059308758020659515228160000000⟩,
  ⟨5, 6, 6, 3, 6, 8, 28353719166323495440036674465782930549086617600000⟩,
  ⟨5, 6, 7, 3, 7, 8, 3502726345567516319245186527488891486522572800000⟩,
  ⟨5, 6, 8, 3, 8, 8, 1761150216932606618501204226283500522700800000000⟩,
  ⟨5, 6, 1, 4, 0, 8, -27509303976401284155301188903067437970576166092800000⟩,
  ⟨5, 6, 2, 4, 1, 8, -11309840323274031224213781677261583907887985459200000⟩,
  ⟨5, 6, 3, 4, 2, 8, -9143479524471132590485387730794305433852968960000000⟩,
  ⟨5, 6, 4, 4, 3, 8, 358062580201511334129820611876400842351732326400000⟩,
  ⟨5, 6, 5, 4, 4, 8, -97371361493161759018673689602702543820318310400000⟩,
  ⟨5, 6, 6, 4, 5, 8, -22558254591623670814129340911369872560514662400000⟩,
  ⟨5, 6, 7, 4, 6, 8, -1150384093992553737313067764594915613343744000000⟩,
  ⟨5, 6, 8, 4, 7, 8, 625607160366759792358686302529680695728537600000⟩,
  ⟨5, 6, 2, 5, 0, 8, 84383568627565241992969800163009967525835728486400000⟩,
  ⟨5, 6, 3, 5, 1, 8, 7592949419827194692052782109818050792461120307200000⟩,
  ⟨5, 6, 4, 5, 2, 8, -2453323593372855259904580616754840076518518947840000⟩,
  ⟨5, 6, 5, 5, 3, 8, 253950108492157391585702932672633361109142732800000⟩,
  ⟨5, 6, 6, 5, 4, 8, -25443029101613679749542480470579817328777625600000⟩,
  ⟨5, 6, 7, 5, 5, 8, -3046725439547827373894895362777418006999859200000⟩,
  ⟨5, 6, 8, 5, 6, 8, 1302678302733508668662731815520865349953126400000⟩,
  ⟨5, 6, 3, 6, 0, 8, 4135124133476908405253552715101448435364213555200000⟩,
  ⟨5, 6, 4, 6, 1, 8, 1316468428775424779695821886731888984771746856960000⟩,
  ⟨5, 6, 5, 6, 2, 8, 3758442458519617506285970439864346729460531200000⟩,
  ⟨5, 6, 6, 6, 3, 8, 94210175612242009796571593868950421888407961600000⟩,
  ⟨5, 6, 7, 6, 4, 8, 1090683773889283859011674001337956086212198400000⟩,
  ⟨5, 6, 8, 6, 5, 8, -1367102763482109498820044600377545943993548800000⟩,
  ⟨5, 6, 4, 7, 0, 8, 25119840184799709280928779644833554908049645240320000⟩,
  ⟨5, 6, 5, 7, 1, 8, -175205655216618654454944868370095868173772390400000⟩,
  ⟨5, 6, 6, 7, 2, 8, -92973905012828104860288643458436255315289702400000⟩,
  ⟨5, 6, 7, 7, 3, 8, 45699174228412150370382894928189622371064217600000⟩,
  ⟨5, 6, 8, 7, 4, 8, 2703065312199284756622304950761713588764672000000⟩
]

def collectedFourData_10_3_45 : List CollectedFourTerm := [
  ⟨6, 0, 4, 0, 7, 3, 20689562349390852969835001772698012048498444206080000⟩,
  ⟨6, 0, 5, 0, 8, 3, 1950354204041596789510755352650894153434215219200000⟩,
  ⟨6, 0, 4, 1, 6, 3, 46355674807469485313820534496676792642654510776320000⟩,
  ⟨6, 0, 5, 1, 7, 3, -15469305564436803732799529802202147110033083596800000⟩,
  ⟨6, 0, 6, 1, 8, 3, -4230765597219899793056672839617180032373148876800000⟩,
  ⟨6, 0, 4, 2, 5, 3, -5882292195737205242387873824383927656743761346560000⟩,
  ⟨6, 0, 5, 2, 6, 3, -10812240248273333934776033167663879953091815014400000⟩,
  ⟨6, 0, 6, 2, 7, 3, -5661248276677054461199200106100629196237910835200000⟩,
  ⟨6, 0, 7, 2, 8, 3, -8850053493381764738967747965499417465902963097600000⟩,
  ⟨6, 0, 4, 3, 4, 3, 4035840009038081717422744560879387247083320770560000⟩,
  ⟨6, 0, 5, 3, 5, 3, 4085510507347009711171572817956253149199073280000000⟩,
  ⟨6, 0, 6, 3, 6, 3, 15000652649297549716727066745756862319178861772800000⟩,
  ⟨6, 0, 7, 3, 7, 3, 4941685044531648171744073917649853395881059942400000⟩,
  ⟨6, 0, 8, 3, 8, 3, 5590462932739829408110298141041835161052774400000000⟩,
  ⟨6, 0, 4, 4, 3, 3, 9020690104863039840284616925912383072674984755200000⟩,
  ⟨6, 0, 5, 4, 4, 3, -14718492113150988475348976354854646405307511603200000⟩,
  ⟨6, 0, 6, 4, 5, 3, -11934538094222283178419877158795079594097718067200000⟩,
  ⟨6, 0, 7, 4, 6, 3, -1622974595187517591509601414854473683411402752000000⟩,
  ⟨6, 0, 8, 4, 7, 3, 1985880367762421206645167505201257540890709196800000⟩,
  ⟨6, 0, 4, 5, 2, 3, -61806715044925380978241347701035143126303501189120000⟩,
  ⟨6, 0, 5, 5, 3, 3, 38386673572785091995113715529041537041823065702400000⟩,
  ⟨6, 0, 6, 5, 4, 3, -13460740005938500427906629033080480318972808396800000⟩,
  ⟨6, 0, 7, 5, 5, 3, -4298353926066760624166732687081525234938517913600000⟩,
  ⟨6, 0, 8, 5, 6, 3, 4135124133476908405253552715101448435364213555200000⟩,
  ⟨6, 0, 4, 6, 1, 3, 33165860901007223299855974764194090051731487457280000⟩,
  ⟨6, 0, 5, 6, 2, 3, 568119874623892796523180876962408240030259609600000⟩,
  ⟨6, 0, 6, 6, 3, 3, 49842283902814393862035956299489300483349990604800000⟩,
  ⟨6, 0, 7, 6, 4, 3, 1538748723708459383048236772273778941416911667200000⟩,
  ⟨6, 0, 8, 6, 5, 3, -4339628301442829991334911102083645600807937638400000⟩,
  ⟨6, 0, 4, 7, 0, 3, 632845503328602921645180672415553966186774145269760000⟩,
  ⟨6, 0, 5, 7, 1, 3, -26483793745313457187385121774678501126625768243200000⟩,
  ⟨6, 0, 6, 7, 2, 3, -49188229817931832202592321391253832021780411187200000⟩,
  ⟨6, 0, 7, 7, 3, 3, 64472900121862366845482918719233638622823238860800000⟩,
  ⟨6, 0, 8, 7, 4, 3, 8580407444712127421640663068455433462398058496000000⟩
]

def collectedFourData_10_3_46 : List CollectedFourTerm := [
  ⟨6, 1, 3, 0, 6, 4, -2295696080762564403615548413374587481056681656320000⟩,
  ⟨6, 1, 4, 0, 7, 4, 32933903262599434081860699114889533147752347729920000⟩,
  ⟨6, 1, 5, 0, 8, 4, 1552299067495770967942821475904967796620420710400000⟩,
  ⟨6, 1, 3, 1, 5, 4, 30777083886973886535964095241515226631128649564160000⟩,
  ⟨6, 1, 4, 1, 6, 4, 73789541025582223370834884515283399087763415367680000⟩,
  ⟨6, 1, 5, 1, 7, 4, -12312116718451335663335573161210276100190083481600000⟩,
  ⟨6, 1, 6, 1, 8, 4, -2244861806041316186082307852965346144592225894400000⟩,
  ⟨6, 1, 3, 2, 4, 4, -40078377361000135030001289268087942029762279505920000⟩,
  ⟨6, 1, 4, 2, 5, 4, -9363506045474977606191978018783814453934099005440000⟩,
  ⟨6, 1, 5, 2, 6, 4, -8605529405968853976495633676227522272923798732800000⟩,
  ⟨6, 1, 6, 2, 7, 4, -3003881859864945938869591308146832302178671001600000⟩,
  ⟨6, 1, 7, 2, 8, 4, -3521906368749828292747846213759007665092663705600000⟩,
  ⟨6, 1, 3, 3, 3, 4, 53570433766794713375732053711604866121164872744960000⟩,
  ⟨6, 1, 4, 3, 4, 4, 6424300436925479602426039904770192009890040381440000⟩,
  ⟨6, 1, 5, 3, 5, 4, 3251683277661536875279828204813799799505551360000000⟩,
  ⟨6, 1, 6, 3, 6, 4, 7959408628128323965498634691664730403721602662400000⟩,
  ⟨6, 1, 7, 3, 7, 4, 1966558964158458523819354612584742419226322534400000⟩,
  ⟨6, 1, 8, 3, 8, 4, 1779793717341945115068867457241199135550341120000000⟩,
  ⟨6, 1, 3, 4, 2, 4, -73335493753324512786982522174967480263108460544000000⟩,
  ⟨6, 1, 4, 4, 3, 4, 14359246960300936070366759966700162023083003084800000⟩,
  ⟨6, 1, 5, 4, 4, 4, -11714539612775306778849898576749077361997538918400000⟩,
  ⟨6, 1, 6, 4, 5, 4, -6332515504538882996188378214688556734100380057600000⟩,
  ⟨6, 1, 7, 4, 6, 4, -645867798130779397558066258735801154679078912000000⟩,
  ⟨6, 1, 8, 4, 7, 4, 632229825053873818602553772899146597279612272640000⟩,
  ⟨6, 1, 3, 5, 1, 4, 60899430381701865717589951044582287202869921710080000⟩,
  ⟨6, 1, 4, 5, 2, 4, -98384699487302218364132876232929500348409582714880000⟩,
  ⟨6, 1, 5, 5, 3, 4, 30552192759560909007837583791726834796964138188800000⟩,
  ⟨6, 1, 6, 5, 4, 4, -7142324580742567557841538967281848504889534054400000⟩,
  ⟨6, 1, 7, 5, 5, 4, -1710543340633605330622955107978321710894651801600000⟩,
  ⟨6, 1, 8, 5, 6, 4, 1316468428775424779695821886731888984771746856960000⟩,
  ⟨6, 1, 3, 6, 0, 4, 33165860901007223299855974764194090051731487457280000⟩,
  ⟨6, 1, 4, 6, 1, 4, 52793830825849247756446787305250010016770655518720000⟩,
  ⟨6, 1, 5, 6, 2, 4, 452170149287239046337784151458151408352834355200000⟩,
  ⟨6, 1, 6, 6, 3, 4, 26446522949137131513088042203995754242232444518400000⟩,
  ⟨6, 1, 7, 6, 4, 4, 612349850087026973907779553807570169970766643200000⟩,
  ⟨6, 1, 8, 6, 5, 4, -1381574885556385587412528776016700731329683128320000⟩,
  ⟨6, 1, 4, 7, 0, 4, 1007371361212427678794095964056729716097615648522240000⟩,
  ⟨6, 1, 5, 7, 1, 4, -21078616514584449553707507794246164926502954598400000⟩,
  ⟨6, 1, 6, 7, 2, 4, -26099479133898824699879975258457060200779717017600000⟩,
  ⟨6, 1, 7, 7, 3, 4, 25657191532318305209994939957431396435193810124800000⟩,
  ⟨6, 1, 8, 7, 4, 4, 2731679906667114010883668252445535448419060940800000⟩
]

def collectedFourData_10_3_47 : List CollectedFourTerm := [
  ⟨6, 2, 2, 0, 5, 5, -244996456555910556867378916501551114004463616000000⟩,
  ⟨6, 2, 3, 0, 6, 5, -39324490127671663061870520023181106098890342400000⟩,
  ⟨6, 2, 4, 0, 7, 5, 282073259733402290351001559559096344518013747200000⟩,
  ⟨6, 2, 5, 0, 8, 5, 8863451027114256524805709475515553154072576000000⟩,
  ⟨6, 2, 2, 1, 4, 5, 844391198339276538118264038088561132993039564800000⟩,
  ⟨6, 2, 3, 1, 5, 5, 527200939886521279018426224445954897636176691200000⟩,
  ⟨6, 2, 4, 1, 6, 5, 631994823248131737776830843371052215260990668800000⟩,
  ⟨6, 2, 5, 1, 7, 5, -70300785370023682552357517734303388248571904000000⟩,
  ⟨6, 2, 6, 1, 8, 5, -9613429089047305729145341793994262972465152000000⟩,
  ⟨6, 2, 2, 2, 3, 5, -314699414378800724037583489025781402204477849600000⟩,
  ⟨6, 2, 3, 2, 4, 5, -686528921695169150068306006749001079413171814400000⟩,
  ⟨6, 2, 4, 2, 5, 5, -80196830959297581301772742266719808950527590400000⟩,
  ⟨6, 2, 5, 2, 6, 5, -49136593617392208361686145358855938278162432000000⟩,
  ⟨6, 2, 6, 2, 7, 5, -12863867688412935549154274009999037356310528000000⟩,
  ⟨6, 2, 7, 2, 8, 5, -12065810748126711054883810345795909056882278400000⟩,
  ⟨6, 2, 2, 3, 2, 5, -168278962488485054700869326970383829909372928000000⟩,
  ⟨6, 2, 3, 3, 3, 5, 917643241825653741027727460991819739936535347200000⟩,
  ⟨6, 2, 4, 3, 4, 5, 55023036634961618248891251800981547065435750400000⟩,
  ⟨6, 2, 5, 3, 5, 5, 18566741480902113955300621604162443306598400000000⟩,
  ⟨6, 2, 6, 3, 6, 5, 34085488127305532897148721730033258009198592000000⟩,
  ⟨6, 2, 7, 3, 7, 5, 6737296737105148583703723867118418381085081600000⟩,
  ⟨6, 2, 8, 3, 8, 5, 5081209794667657166382698457293040019046400000000⟩,
  ⟨6, 2, 2, 4, 1, 5, -388461437859672572903256828146495523777832550400000⟩,
  ⟨6, 2, 3, 4, 2, 5, -1256211971731290400495408851141688224204718080000000⟩,
  ⟨6, 2, 4, 4, 3, 5, 122984499137966532301023435226256968639315968000000⟩,
  ⟨6, 2, 5, 4, 4, 5, -66888688099599603851032749465910652065284096000000⟩,
  ⟨6, 2, 6, 4, 5, 5, -27118457178230748680371261274983398541099008000000⟩,
  ⟨6, 2, 7, 4, 6, 5, -2212698977378420373189532110114706862112768000000⟩,
  ⟨6, 2, 8, 4, 7, 5, 1804980177333415568960722777270347493067980800000⟩,
  ⟨6, 2, 2, 5, 0, 5, 2898339982160340144278816847836017119416077516800000⟩,
  ⟨6, 2, 3, 5, 1, 5, 1043186451766980367581445189728893243527633305600000⟩,
  ⟨6, 2, 4, 5, 2, 5, -842648157158767383002492439726671241109359820800000⟩,
  ⟨6, 2, 5, 5, 3, 5, 174449543883437682409041581943017995681923072000000⟩,
  ⟨6, 2, 6, 5, 4, 5, -30586395431178041900350574556456334972157952000000⟩,
  ⟨6, 2, 7, 5, 5, 5, -5860204691324541709249638439060460055979622400000⟩,
  ⟨6, 2, 8, 5, 6, 5, 3758442458519617506285970439864346729460531200000⟩,
  ⟨6, 2, 3, 6, 0, 5, 568119874623892796523180876962408240030259609600000⟩,
  ⟨6, 2, 4, 6, 1, 5, 452170149287239046337784151458151408352834355200000⟩,
  ⟨6, 2, 5, 6, 2, 5, 2581840096442178863622834185392332931596288000000⟩,
  ⟨6, 2, 6, 6, 3, 5, 113254977361716837847070065917181368647811072000000⟩,
  ⟨6, 2, 7, 6, 4, 5, 2097868775942651332271528535425606635801804800000⟩,
  ⟨6, 2, 8, 6, 5, 5, -3944317688142065619786179834236409269872230400000⟩,
  ⟨6, 2, 4, 7, 0, 5, 8627963753751437574602754033462103099465688678400000⟩,
  ⟨6, 2, 5, 7, 1, 5, -120356501597170521297920865725273100880183296000000⟩,
  ⟨6, 2, 6, 7, 2, 5, -111768791842587161038596913720568884450295808000000⟩,
  ⟨6, 2, 7, 7, 3, 5, 87899786349880071380900025011854830686384947200000⟩,
  ⟨6, 2, 8, 7, 4, 5, 7798790703893137123107331794437037386366976000000⟩
]

def collectedFourData_10_3_48 : List CollectedFourTerm := [
  ⟨6, 3, 1, 0, 4, 6, 1745484983078964334360290884814777997930266624000000⟩,
  ⟨6, 3, 2, 0, 5, 6, -42988050544534406435103160768086869008623599616000000⟩,
  ⟨6, 3, 3, 0, 6, 6, -3450015549226135734344605575088786602544280371200000⟩,
  ⟨6, 3, 4, 0, 7, 6, 16497897856893914462127531670521321075142714982400000⟩,
  ⟨6, 3, 5, 0, 8, 6, 388804073035276788048781078552535480238342144000000⟩,
  ⟨6, 3, 1, 1, 3, 6, -7049473551085663358338656713391747359905834598400000⟩,
  ⟨6, 3, 2, 1, 4, 6, 148160230657397592889282668424860018631984860364800000⟩,
  ⟨6, 3, 3, 1, 5, 6, 46252384564173949158299708030469851884998465945600000⟩,
  ⟨6, 3, 4, 1, 6, 6, 36964106593754923888502135422399932803495598489600000⟩,
  ⟨6, 3, 5, 1, 7, 6, -3083813698053804336960426082503353402419838976000000⟩,
  ⟨6, 3, 6, 1, 8, 6, -337362083840549280754836633303390602658211430400000⟩,
  ⟨6, 3, 1, 2, 2, 6, -1230685029748226549504507892007994512308279705600000⟩,
  ⟨6, 3, 2, 2, 3, 6, -55218408142829491620026164476919418893505239449600000⟩,
  ⟨6, 3, 3, 2, 4, 6, -60230544557654833844742304331128884536664077107200000⟩,
  ⟨6, 3, 4, 2, 5, 6, -4690551408040483380843306054473034036084001996800000⟩,
  ⟨6, 3, 5, 2, 6, 6, -2155425429110909220682265631639027995123908608000000⟩,
  ⟨6, 3, 6, 2, 7, 6, -451429055065945413728221391417070252652599705600000⟩,
  ⟨6, 3, 7, 2, 8, 6, -352852506244914113927972889598836225937401446400000⟩,
  ⟨6, 3, 1, 3, 1, 6, 6906629206574399721953759691422625196922634240000000⟩,
  ⟨6, 3, 2, 3, 2, 6, -29526894579334210866110782198088001706606460928000000⟩,
  ⟨6, 3, 3, 3, 3, 6, 80506662455440998694337368221511903265060133273600000⟩,
  ⟨6, 3, 4, 3, 4, 6, 3218186789622277034997223356149881014223424716800000⟩,
  ⟨6, 3, 5, 3, 5, 6, 814448535754820791517966467359422996388249600000000⟩,
  ⟨6, 3, 6, 3, 6, 6, 1196155003260097516759374833638368588163606118400000⟩,
  ⟨6, 3, 7, 3, 7, 6, 197025470449411744635505709935968926033353113600000⟩,
  ⟨6, 3, 8, 3, 8, 6, 127367033647985147618578255071690930467635200000000⟩,
  ⟨6, 3, 1, 4, 0, 6, -55263417110840099686797106905088705710156624691200000⟩,
  ⟨6, 3, 2, 4, 1, 6, -68160985510021845474906688165998520027075470950400000⟩,
  ⟨6, 3, 3, 4, 2, 6, -110209968941142904270359928253673738003850199040000000⟩,
  ⟨6, 3, 4, 4, 3, 6, 7193116095716048377655481607120019091049414656000000⟩,
  ⟨6, 3, 5, 4, 4, 6, -2934138666029020214514249230544300088202625024000000⟩,
  ⟨6, 3, 6, 4, 5, 6, -951662423412671226597163586453462701500373401600000⟩,
  ⟨6, 3, 7, 4, 6, 6, -64708157291025903431103257105079302910640128000000⟩,
  ⟨6, 3, 8, 4, 7, 6, 45244140720508845937971912966693215560689254400000⟩,
  ⟨6, 3, 2, 5, 0, 6, 508554235436136201715124797294486999273315290316800000⟩,
  ⟨6, 3, 3, 5, 1, 6, 91520817374961698631547308266390983129372085452800000⟩,
  ⟨6, 3, 4, 5, 2, 6, -49284796578181316166122306588389766267145918873600000⟩,
  ⟨6, 3, 5, 5, 3, 6, 7652402319766604251315699413799400188850208768000000⟩,
  ⟨6, 3, 6, 5, 4, 6, -1073362065112591986665266355381908309079909990400000⟩,
  ⟨6, 3, 7, 5, 5, 6, -171375795262088312096849672432751621429421670400000⟩,
  ⟨6, 3, 8, 5, 6, 6, 94210175612242009796571593868950421888407961600000⟩,
  ⟨6, 3, 3, 6, 0, 6, 49842283902814393862035956299489300483349990604800000⟩,
  ⟨6, 3, 4, 6, 1, 6, 26446522949137131513088042203995754242232444518400000⟩,
  ⟨6, 3, 5, 6, 2, 6, 113254977361716837847070065917181368647811072000000⟩,
  ⟨6, 3, 6, 6, 3, 6, 3974433556866174036040670658561868893922944614400000⟩,
  ⟨6, 3, 7, 6, 4, 6, 61350063482409675866760760069215976413777100800000⟩,
  ⟨6, 3, 8, 6, 5, 6, -98869376389681620810954892050744801448112947200000⟩,
  ⟨6, 3, 4, 7, 0, 6, 504632253539055841399756028400419640585415871692800000⟩,
  ⟨6, 3, 5, 7, 1, 6, -5279557352334369802990156138800836571587149824000000⟩,
  ⟨6, 3, 6, 7, 2, 6, -3922279155032756707092281193959472498780772761600000⟩,
  ⟨6, 3, 7, 7, 3, 6, 2570540891068015475773585403272653172271952691200000⟩,
  ⟨6, 3, 8, 7, 4, 6, 195486680955144377663705760376789498035437568000000⟩
]
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1013. -/
namespace LaughlinFock
def collectedFourData_10_3_49 : List CollectedFourTerm := [
  ⟨6, 4, 0, 0, 3, 7, -5841091707999553272203905834242560784758892134400000⟩,
  ⟨6, 4, 1, 0, 4, 7, 161661700447080332894015412167433112894046208000000⟩,
  ⟨6, 4, 2, 0, 5, 7, -1990713588860500398189965178013550071498407936000000⟩,
  ⟨6, 4, 3, 0, 6, 7, -106510107632653938111228298495056594533665996800000⟩,
  ⟨6, 4, 4, 0, 7, 7, 381996729734548527987612435015228971470238515200000⟩,
  ⟨6, 4, 5, 0, 8, 7, 7201978613045468142350134220998688678451609600000⟩,
  ⟨6, 4, 0, 1, 2, 7, 2284756639362331346857832112656831919330793881600000⟩,
  ⟨6, 4, 1, 1, 3, 7, -652901567514471265091428755511696913777609932800000⟩,
  ⟨6, 4, 2, 1, 4, 7, 6861083039642219590473759299671971459079392460800000⟩,
  ⟨6, 4, 3, 1, 5, 7, 1427920073955053696053202617025010728287233638400000⟩,
  ⟨6, 4, 4, 1, 6, 7, 855876788597845601835733187682464853215988940800000⟩,
  ⟨6, 4, 5, 1, 7, 7, -57122756268000943685205654069455132052317798400000⟩,
  ⟨6, 4, 6, 1, 8, 7, -5207581146857910200319635439131481397316812800000⟩,
  ⟨6, 4, 0, 2, 1, 7, 2360408829858797065251417910997931057035083776000000⟩,
  ⟨6, 4, 1, 2, 2, 7, -113982438435486328893687351902761550605398835200000⟩,
  ⟨6, 4, 2, 2, 3, 7, -2557083516297110968690258118632805867267398041600000⟩,
  ⟨6, 4, 3, 2, 4, 7, -1859458803032972982391466098629253157293444300800000⟩,
  ⟨6, 4, 4, 2, 5, 7, -108606279058427082296949435285972999194699366400000⟩,
  ⟨6, 4, 5, 2, 6, 7, -39925836479245585813154405944071984268915507200000⟩,
  ⟨6, 4, 6, 2, 7, 7, -6968339208553162165686818590692710284473139200000⟩,
  ⟨6, 4, 7, 2, 8, 7, -4668594911160514532985014706341676893759078400000⟩,
  ⟨6, 4, 0, 3, 0, 7, -13189383896015573905027841731744905485613426278400000⟩,
  ⟨6, 4, 1, 3, 1, 7, 639671743221050368079189097698437976115118080000000⟩,
  ⟨6, 4, 2, 3, 2, 7, -1367347193728593634266975355608447632422207488000000⟩,
  ⟨6, 4, 3, 3, 3, 7, 2485430329494644239072739160087009943932528230400000⟩,
  ⟨6, 4, 4, 3, 4, 7, 74514755757015248439775825727628686441997926400000⟩,
  ⟨6, 4, 5, 3, 5, 7, 15086366997498552550203872616116596129136640000000⟩,
  ⟨6, 4, 6, 3, 6, 7, 18464061440411169080038620688114818659175628800000⟩,
  ⟨6, 4, 7, 3, 7, 7, 2606845898582555771691690135699664206928281600000⟩,
  ⟨6, 4, 8, 3, 8, 7, 1474545143616274564637424979585767623884800000000⟩,
  ⟨6, 4, 1, 4, 0, 7, -5118335631221251186301590582316965060936099430400000⟩,
  ⟨6, 4, 2, 4, 1, 7, -3156435296928716986982191530620186459717920358400000⟩,
  ⟨6, 4, 3, 4, 2, 7, -3402441376458609325133528726924871225374146560000000⟩,
  ⟨6, 4, 4, 4, 3, 7, 166551329690545005549428659107765569231781888000000⟩,
  ⟨6, 4, 5, 4, 4, 7, -54350263760054438323128234797283243281979801600000⟩,
  ⟨6, 4, 6, 4, 5, 7, -14690030479771616786561212678410306816521011200000⟩,
  ⟨6, 4, 7, 4, 6, 7, -856154252819089849855460361961643094048768000000⟩,
  ⟨6, 4, 8, 4, 7, 7, 523797454221177325340951209736636376652185600000⟩,
  ⟨6, 4, 2, 5, 0, 7, 23550400967973075137464922172985219686798773452800000⟩,
  ⟨6, 4, 3, 5, 1, 7, 2825463239266315831059672442808057560195871539200000⟩,
  ⟨6, 4, 4, 5, 2, 7, -1141153332491431134705312836921142105302944972800000⟩,
  ⟨6, 4, 5, 5, 3, 7, 141748612392695216780870136297267681622700851200000⟩,
  ⟨6, 4, 6, 5, 4, 7, -16568607800853764858715193212687113752726732800000⟩,
  ⟨6, 4, 7, 5, 5, 7, -2267474798949947459323207602736267098744422400000⟩,
  ⟨6, 4, 8, 5, 6, 7, 1090683773889283859011674001337956086212198400000⟩,
  ⟨6, 4, 3, 6, 0, 7, 1538748723708459383048236772273778941416911667200000⟩,
  ⟨6, 4, 4, 6, 1, 7, 612349850087026973907779553807570169970766643200000⟩,
  ⟨6, 4, 5, 6, 2, 7, 2097868775942651332271528535425606635801804800000⟩,
  ⟨6, 4, 6, 6, 3, 7, 61350063482409675866760760069215976413777100800000⟩,
  ⟨6, 4, 7, 6, 4, 7, 811723281269681104008733134453615094451404800000⟩,
  ⟨6, 4, 8, 6, 5, 7, -1144623962984795787393595418532294702189772800000⟩,
  ⟨6, 4, 4, 7, 0, 7, 11684389868491257501615964378937512740723779174400000⟩,
  ⟨6, 4, 5, 7, 1, 7, -97795423903414664511573434489349525105908121600000⟩,
  ⟨6, 4, 6, 7, 2, 7, -60544998856825599139590702664253756136436531200000⟩,
  ⟨6, 4, 7, 7, 3, 7, 34010851306354089105102514719243273090839347200000⟩,
  ⟨6, 4, 8, 7, 4, 7, 2263175389957997788934560563515227983839232000000⟩
]

def collectedFourData_10_3_50 : List CollectedFourTerm := [
  ⟨6, 5, 0, 0, 3, 8, 65892933646157854939917283685909050594444915507200000⟩,
  ⟨6, 5, 1, 0, 4, 8, -911846982824783847976349333513348834710781952000000⟩,
  ⟨6, 5, 2, 0, 5, 8, 7485698734458776147635382946612014146551545856000000⟩,
  ⟨6, 5, 3, 0, 6, 8, 300383207700363244818879822125747899570166169600000⟩,
  ⟨6, 5, 4, 0, 7, 8, -861855503175052237797290588253858742582923755520000⟩,
  ⟨6, 5, 5, 0, 8, 8, -13540833420475413879775804815007785524448460800000⟩,
  ⟨6, 5, 0, 1, 2, 8, -25774174616868081084513565981299759812172369100800000⟩,
  ⟨6, 5, 1, 1, 3, 8, 3682667711481409791042445552062977512500835123200000⟩,
  ⟨6, 5, 2, 1, 4, 8, -25799794060915207448845878197330679295772511436800000⟩,
  ⟨6, 5, 3, 1, 5, 8, -4027065803310289603948371458932496862811049164800000⟩,
  ⟨6, 5, 4, 1, 6, 8, -1931016846153199524250822701990960274000136110080000⟩,
  ⟨6, 5, 5, 1, 7, 8, 107399614564578177963780755901284716572259123200000⟩,
  ⟨6, 5, 6, 1, 8, 8, 8392335252206030745231637546650430461915955200000⟩,
  ⟨6, 5, 0, 2, 1, 8, -26627601513374957620807165502812411238692159488000000⟩,
  ⟨6, 5, 1, 2, 2, 8, 642913827424651336039007813414719586837515468800000⟩,
  ⟨6, 5, 2, 2, 3, 8, 9615424814981774258584815253009430738133162393600000⟩,
  ⟨6, 5, 3, 2, 4, 8, 5244105111301959367667338999084793360167836057600000⟩,
  ⟨6, 5, 4, 2, 5, 8, 245035917849129118667670862822133018579844464640000⟩,
  ⟨6, 5, 5, 2, 6, 8, 75066746235447605332473211676244720196622745600000⟩,
  ⟨6, 5, 6, 2, 7, 8, 11229904468134028628635020073160913927851212800000⟩,
  ⟨6, 5, 7, 2, 8, 8, 6583260246551703711692692763516409838200422400000⟩,
  ⟨6, 5, 0, 3, 0, 8, 148788487039779867887319887745645098807160156979200000⟩,
  ⟨6, 5, 1, 3, 1, 8, -3608045365360493770488098732381438056354283520000000⟩,
  ⟨6, 5, 2, 3, 2, 8, 5141648308895504443853863736780103372502990848000000⟩,
  ⟨6, 5, 3, 3, 3, 8, -7009490005063937456544637035777224172454595788800000⟩,
  ⟨6, 5, 4, 3, 4, 8, -168119115473988387656899058549190505301425520640000⟩,
  ⟨6, 5, 5, 3, 5, 8, -28364702730893271356892014185255917028638720000000⟩,
  ⟨6, 5, 6, 3, 6, 8, -29755963345622876158435982413983106160866099200000⟩,
  ⟨6, 5, 7, 3, 7, 8, -3675955035635956360467275966671313559984537600000⟩,
  ⟨6, 5, 8, 3, 8, 8, -1848248584031437090096397713235607394713600000000⟩,
  ⟨6, 5, 1, 4, 0, 8, 28869787274948669475718023230952976538882644377600000⟩,
  ⟨6, 5, 2, 4, 1, 8, 11869172863357619322372067877254045409347004006400000⟩,
  ⟨6, 5, 3, 4, 2, 8, 9595673850955153053489744348946522584719032320000000⟩,
  ⟨6, 5, 4, 4, 3, 8, -375770703991805295260356633239527105745439948800000⟩,
  ⟨6, 5, 5, 4, 4, 8, 102186899944512876146908564639915418181225676800000⟩,
  ⟨6, 5, 6, 4, 5, 8, 23673881822418431825527057918735390396435660800000⟩,
  ⟨6, 5, 7, 4, 6, 8, 1207276785575518879731099640927088592027648000000⟩,
  ⟨6, 5, 8, 4, 7, 8, -656546805145150707420569799456068834898739200000⟩,
  ⟨6, 5, 2, 5, 0, 8, -88556790745002757089465865115293999934691134668800000⟩,
  ⟨6, 5, 3, 5, 1, 8, -7968461678561605586849952208291965113301624422400000⟩,
  ⟨6, 5, 4, 5, 2, 8, 2574653663285902141505498062578717071221488353280000⟩,
  ⟨6, 5, 5, 5, 3, 8, -266509309610595636158408647852038095726287257600000⟩,
  ⟨6, 5, 6, 5, 4, 8, 26701323974755313574405725537854165504701235200000⟩,
  ⟨6, 5, 7, 5, 5, 8, 3197402427934012790602667641467068928648806400000⟩,
  ⟨6, 5, 8, 5, 6, 8, -1367102763482109498820044600377545943993548800000⟩,
  ⟨6, 5, 3, 6, 0, 8, -4339628301442829991334911102083645600807937638400000⟩,
  ⟨6, 5, 4, 6, 1, 8, -1381574885556385587412528776016700731329683128320000⟩,
  ⟨6, 5, 5, 6, 2, 8, -3944317688142065619786179834236409269872230400000⟩,
  ⟨6, 5, 6, 6, 3, 8, -98869376389681620810954892050744801448112947200000⟩,
  ⟨6, 5, 7, 6, 4, 8, -1144623962984795787393595418532294702189772800000⟩,
  ⟨6, 5, 8, 6, 5, 8, 1434713360926192764480144771266433053727129600000⟩,
  ⟨6, 5, 4, 7, 0, 8, -26362151624700785090814030353554613872841132605440000⟩,
  ⟨6, 5, 5, 7, 1, 8, 183870518854671471420733882365221079064825036800000⟩,
  ⟨6, 5, 6, 7, 2, 8, 97571965548245212730604030454396757193051340800000⟩,
  ⟨6, 5, 7, 7, 3, 8, -47959244615816229500423472744130742488085299200000⟩,
  ⟨6, 5, 8, 7, 4, 8, -2836746455687488025957254114446756412391424000000⟩
]

def collectedFourData_10_3_51 : List CollectedFourTerm := [
  ⟨7, 0, 3, 0, 6, 4, -43804710695013649040193559651143610563646917181440000⟩,
  ⟨7, 0, 4, 0, 7, 4, 628419465697098731255525434860159315812092099952640000⟩,
  ⟨7, 0, 5, 0, 8, 4, 29619779435788696968286758682718525568368561356800000⟩,
  ⟨7, 0, 3, 1, 5, 4, 587264693703371269190082751381164865700210902302720000⟩,
  ⟨7, 0, 4, 1, 6, 4, 1407995389298126466623597920441734233139209369026560000⟩,
  ⟨7, 0, 5, 1, 7, 4, -234930361825530513816113656979593250199376704307200000⟩,
  ⟨7, 0, 6, 1, 8, 4, -42834730079454358157158076629984386572484398284800000⟩,
  ⟨7, 0, 3, 2, 4, 4, -764744837148055038527032846473574272778430463344640000⟩,
  ⟨7, 0, 4, 2, 5, 4, -178667235985696084176847912678336546835251310100480000⟩,
  ⟨7, 0, 5, 2, 6, 4, -164204107488253455805803827325882945429304875417600000⟩,
  ⟨7, 0, 6, 2, 7, 4, -57317768208096168809095369426987536156099556147200000⟩,
  ⟨7, 0, 7, 2, 8, 4, -67202314309290537754231568787725725012669444915200000⟩,
  ⟨7, 0, 3, 3, 3, 4, 1022189902498481884632772659283997535869329546936320000⟩,
  ⟨7, 0, 4, 3, 4, 4, 122583570366985401466256178404280944575566556692480000⟩,
  ⟨7, 0, 5, 3, 5, 4, 62046124677994482285621133509225427995061125120000000⟩,
  ⟨7, 0, 6, 3, 6, 4, 151875326695135529876843514207512351047502580940800000⟩,
  ⟨7, 0, 7, 3, 7, 4, 37524368844604309933905906220181958196990889164800000⟩,
  ⟨7, 0, 8, 3, 8, 4, 33960657744848183001014907483545605363508183040000000⟩,
  ⟨7, 0, 3, 4, 2, 4, -1399331607724520949342133893339837699895798530048000000⟩,
  ⟨7, 0, 4, 4, 3, 4, 273992129953586887453153492424482744295312955801600000⟩,
  ⟨7, 0, 5, 4, 4, 4, -223527854127992912256416690915820672291420556492800000⟩,
  ⟨7, 0, 6, 4, 5, 4, -120832200730974731941505300121256898916420629299200000⟩,
  ⟨7, 0, 7, 4, 6, 4, -12323953628455235421042864825954096290834939904000000⟩,
  ⟨7, 0, 8, 4, 7, 4, 12063724293175892874376222591502345118403138682880000⟩,
  ⟨7, 0, 3, 5, 1, 4, 1162036190990685244935085531298604335080318288527360000⟩,
  ⟨7, 0, 4, 5, 2, 4, -1877301326587432336284891449426530543295672572968960000⟩,
  ⟨7, 0, 5, 5, 3, 4, 582973493811211058823911355727944491583195945369600000⟩,
  ⟨7, 0, 6, 5, 4, 4, -136284356004731788085442876759568603323139149004800000⟩,
  ⟨7, 0, 7, 5, 5, 4, -32639275205299700361985365239988049336081789747200000⟩,
  ⟨7, 0, 8, 5, 6, 4, 25119840184799709280928779644833554908049645240320000⟩,
  ⟨7, 0, 3, 6, 0, 4, 632845503328602921645180672415553966186774145269760000⟩,
  ⟨7, 0, 4, 6, 1, 4, 1007371361212427678794095964056729716097615648522240000⟩,
  ⟨7, 0, 5, 6, 2, 4, 8627963753751437574602754033462103099465688678400000⟩,
  ⟨7, 0, 6, 6, 3, 4, 504632253539055841399756028400419640585415871692800000⟩,
  ⟨7, 0, 7, 6, 4, 4, 11684389868491257501615964378937512740723779174400000⟩,
  ⟨7, 0, 8, 6, 5, 4, -26362151624700785090814030353554613872841132605440000⟩,
  ⟨7, 0, 4, 7, 0, 4, 19221887169705217092348377750122764618862963017646080000⟩,
  ⟨7, 0, 5, 7, 1, 4, -402205982756132422528236301671695157455793999052800000⟩,
  ⟨7, 0, 6, 7, 2, 4, -498010229808476452305546044629775365927054029619200000⟩,
  ⟨7, 0, 7, 7, 3, 4, 489570837245332581167915868783662347697532803481600000⟩,
  ⟨7, 0, 8, 7, 4, 4, 52123819448777839283525897452737723767386118553600000⟩
]

def collectedFourData_10_3_52 : List CollectedFourTerm := [
  ⟨7, 1, 2, 0, 5, 5, 11420891811001795755134042955241607401436086272000000⟩,
  ⟨7, 1, 3, 0, 6, 5, 1833172420469079590352203595404265546507406540800000⟩,
  ⟨7, 1, 4, 0, 7, 5, -13149284799784902031752469697321382216238261862400000⟩,
  ⟨7, 1, 5, 0, 8, 5, -413183589166251240594766346187590074569326592000000⟩,
  ⟨7, 1, 2, 1, 4, 5, -39362612251472506350124822834670810359473478041600000⟩,
  ⟨7, 1, 3, 1, 5, 5, -24576293803369138101516098464892463311413995110400000⟩,
  ⟨7, 1, 4, 1, 6, 5, -29461424066690166464911694569177642471983258009600000⟩,
  ⟨7, 1, 5, 1, 7, 5, 3277180720188372703724264763329946350222573568000000⟩,
  ⟨7, 1, 6, 1, 8, 5, 448144985858972174324297007081274674128093184000000⟩,
  ⟨7, 1, 2, 2, 3, 5, 14670203867971807570345325706424737646649750323200000⟩,
  ⟨7, 1, 3, 2, 4, 5, 32003616093177700407154151429631879429493673164800000⟩,
  ⟨7, 1, 4, 2, 5, 5, 3738500314849718653054612595251920040987774156800000⟩,
  ⟨7, 1, 5, 2, 6, 5, 2290578923280591341100256964406794294283730944000000⟩,
  ⟨7, 1, 6, 2, 7, 5, 599669249121887009421314935629499857031397376000000⟩,
  ⟨7, 1, 7, 2, 8, 5, 562466580552074170022643218678788372554370252800000⟩,
  ⟨7, 1, 2, 3, 2, 5, 7844586210209216423638057050467079205920178176000000⟩,
  ⟨7, 1, 3, 3, 3, 5, -42777370470237975702618538072196396497221609062400000⟩,
  ⟨7, 1, 4, 3, 4, 5, -2564984642450431646724325939958803618664860876800000⟩,
  ⟨7, 1, 5, 3, 5, 5, -865517602650839712627807843396033113279692800000000⟩,
  ⟨7, 1, 6, 3, 6, 5, -1588948173780234728092404959144972517233393664000000⟩,
  ⟨7, 1, 7, 3, 7, 5, -314069591922989727246281736341680676276482867200000⟩,
  ⟨7, 1, 8, 3, 8, 5, -236868516996932611215227265481087646485708800000000⟩,
  ⟨7, 1, 2, 4, 1, 5, 18108735599320996485968992044996079950670646476800000⟩,
  ⟨7, 1, 3, 4, 2, 5, 58560279697572589293257230060145636351001231360000000⟩,
  ⟨7, 1, 4, 4, 3, 5, -5733114179814342627510100353441590785244921856000000⟩,
  ⟨7, 1, 5, 4, 4, 5, 3118120485922352640062234404786927487189778432000000⟩,
  ⟨7, 1, 6, 4, 5, 5, 1264169163373911986690111136208266014842945536000000⟩,
  ⟨7, 1, 7, 4, 6, 5, 103148412781987170313205906012044444047507456000000⟩,
  ⟨7, 1, 8, 4, 7, 5, -84141965219090223287816221824146217939605913600000⟩,
  ⟨7, 1, 2, 5, 0, 5, -135110637243849314957996640724531557201929148825600000⟩,
  ⟨7, 1, 3, 5, 1, 5, -48629762943590201441262339078530176164859949875200000⟩,
  ⟨7, 1, 4, 5, 2, 5, 39281357669163178445202848775132835683052919193600000⟩,
  ⟨7, 1, 5, 5, 3, 5, -8132237482857936388047077168753249105240653824000000⟩,
  ⟨7, 1, 6, 5, 4, 5, 1425832512105271811341224945323333530926710784000000⟩,
  ⟨7, 1, 7, 5, 5, 5, 273182578682189938296394631359513712594308300800000⟩,
  ⟨7, 1, 8, 5, 6, 5, -175205655216618654454944868370095868173772390400000⟩,
  ⟨7, 1, 3, 6, 0, 5, -26483793745313457187385121774678501126625768243200000⟩,
  ⟨7, 1, 4, 6, 1, 5, -21078616514584449553707507794246164926502954598400000⟩,
  ⟨7, 1, 5, 6, 2, 5, -120356501597170521297920865725273100880183296000000⟩,
  ⟨7, 1, 6, 6, 3, 5, -5279557352334369802990156138800836571587149824000000⟩,
  ⟨7, 1, 7, 6, 4, 5, -97795423903414664511573434489349525105908121600000⟩,
  ⟨7, 1, 8, 6, 5, 5, 183870518854671471420733882365221079064825036800000⟩,
  ⟨7, 1, 4, 7, 0, 5, -402205982756132422528236301671695157455793999052800000⟩,
  ⟨7, 1, 5, 7, 1, 5, 5610605976981782402763805220802351166056824832000000⟩,
  ⟨7, 1, 6, 7, 2, 5, 5210276497159290781628241631996100938234331136000000⟩,
  ⟨7, 1, 7, 7, 3, 5, -4097585590520793684953032695055763135195932262400000⟩,
  ⟨7, 1, 8, 7, 4, 5, -363552788223627313836562318381713368014651392000000⟩
]

def collectedFourData_10_3_53 : List CollectedFourTerm := [
  ⟨7, 2, 1, 0, 4, 6, -1722579901411559006665734181722674435337486336000000⟩,
  ⟨7, 2, 2, 0, 5, 6, 42423940960097744392811153226807061875234177024000000⟩,
  ⟨7, 2, 3, 0, 6, 6, 3404742809171134096606864504211393300730268876800000⟩,
  ⟨7, 2, 4, 0, 7, 6, -16281404617813683887553613062347406803199433113600000⟩,
  ⟨7, 2, 5, 0, 8, 6, -383702001615685572472417829933001384306671616000000⟩,
  ⟨7, 2, 1, 1, 3, 6, 6956967016245697768299374499971871770114890137600000⟩,
  ⟨7, 2, 2, 1, 4, 6, -146216001852241623424209163678016873434801451827200000⟩,
  ⟨7, 2, 3, 1, 5, 6, -45645438840764815242407359210574825863824959078400000⟩,
  ⟨7, 2, 4, 1, 6, 6, -36479046058430725216974416061292791958669256294400000⟩,
  ⟨7, 2, 5, 1, 7, 6, 3043346432344999237664584672323830057023832064000000⟩,
  ⟨7, 2, 6, 1, 8, 6, 332935058597270950370042998368700107656370585600000⟩,
  ⟨7, 2, 1, 2, 2, 6, 1214535397189651257937246961531671670096815718400000⟩,
  ⟨7, 2, 2, 2, 3, 6, 54493806006279107370347592539063952281440773734400000⟩,
  ⟨7, 2, 3, 2, 4, 6, 59440170790283975788759641149351626222569573580800000⟩,
  ⟨7, 2, 4, 2, 5, 6, 4628999768176578611633294839131944653564359475200000⟩,
  ⟨7, 2, 5, 2, 6, 6, 2127140914514455611059599432957177837714931712000000⟩,
  ⟨7, 2, 6, 2, 7, 6, 445505188935005848764753762417748843365295718400000⟩,
  ⟨7, 2, 7, 2, 8, 6, 348222208333194538977434809977883654503373209600000⟩,
  ⟨7, 2, 1, 3, 1, 6, -6815997142960755452370627567740941923369615360000000⟩,
  ⟨7, 2, 2, 3, 2, 6, 29139428666833764111700276834800199234530312192000000⟩,
  ⟨7, 2, 3, 3, 3, 6, -79450215853958728135719725054446837376945120870400000⟩,
  ⟨7, 2, 4, 3, 4, 6, -3175956216485384848567114045712895437402485555200000⟩,
  ⟨7, 2, 5, 3, 5, 6, -803760955852267759566116289669134501176934400000000⟩,
  ⟨7, 2, 6, 3, 6, 6, -1180458490083445022523170130883695317874219417600000⟩,
  ⟨7, 2, 7, 3, 7, 6, -194440008795515309008492682509962034754774630400000⟩,
  ⟨7, 2, 8, 3, 8, 6, -125695663034245365330039175390050032340172800000000⟩,
  ⟨7, 2, 1, 4, 0, 6, 54538224345267957778693925892147925884911537356800000⟩,
  ⟨7, 2, 2, 4, 1, 6, 67266544735811384890089356719676435510691731865600000⟩,
  ⟨7, 2, 3, 4, 2, 6, 108763741466469246478491622802681042871842242560000000⟩,
  ⟨7, 2, 4, 4, 3, 6, -7098724615289287074676517318160156837317443584000000⟩,
  ⟨7, 2, 5, 4, 4, 6, 2895635507067241820372505611332664020420263936000000⟩,
  ⟨7, 2, 6, 4, 5, 6, 939174257808623756691429937921696718423221862400000⟩,
  ⟨7, 2, 7, 4, 6, 6, 63859026166056948749212487049676738623700992000000⟩,
  ⟨7, 2, 8, 4, 7, 6, -44650425650931560593898135473498348324493721600000⟩,
  ⟨7, 2, 2, 5, 0, 6, -501880745599275996257717741215428362945812443955200000⟩,
  ⟨7, 2, 3, 5, 1, 6, -90319837809647184758065419112664615599335486259200000⟩,
  ⟨7, 2, 4, 5, 2, 6, 48638058106336421229459373844543047997157959270400000⟩,
  ⟨7, 2, 5, 5, 3, 6, -7551983867711570688691385308163685555426557952000000⟩,
  ⟨7, 2, 6, 5, 4, 6, 1059276899099458473148631804347396857429334425600000⟩,
  ⟨7, 2, 7, 5, 5, 6, 169126920809229678171088144304932888432449945600000⟩,
  ⟨7, 2, 8, 5, 6, 6, -92973905012828104860288643458436255315289702400000⟩,
  ⟨7, 2, 3, 6, 0, 6, -49188229817931832202592321391253832021780411187200000⟩,
  ⟨7, 2, 4, 6, 1, 6, -26099479133898824699879975258457060200779717017600000⟩,
  ⟨7, 2, 5, 6, 2, 6, -111768791842587161038596913720568884450295808000000⟩,
  ⟨7, 2, 6, 6, 3, 6, -3922279155032756707092281193959472498780772761600000⟩,
  ⟨7, 2, 7, 6, 4, 6, -60544998856825599139590702664253756136436531200000⟩,
  ⟨7, 2, 8, 6, 5, 6, 97571965548245212730604030454396757193051340800000⟩,
  ⟨7, 2, 4, 7, 0, 6, -498010229808476452305546044629775365927054029619200000⟩,
  ⟨7, 2, 5, 7, 1, 6, 5210276497159290781628241631996100938234331136000000⟩,
  ⟨7, 2, 6, 7, 2, 6, 3870809147992127495355358924182845830015116902400000⟩,
  ⟨7, 2, 7, 7, 3, 6, -2536809034529520040812255204413368198545329356800000⟩,
  ⟨7, 2, 8, 7, 4, 6, -192921412026694921649977904906450137516081152000000⟩
]

def collectedFourData_10_3_54 : List CollectedFourTerm := [
  ⟨7, 3, 0, 0, 3, 7, -244739193924325927987447259472941140439939520921600000⟩,
  ⟨7, 3, 1, 0, 4, 7, 6773554710957348848321948303121094404275699712000000⟩,
  ⟨7, 3, 2, 0, 5, 7, -83410030766111385969204955996123238196213448704000000⟩,
  ⟨7, 3, 3, 0, 6, 7, -4462727036301980445369031303544040512810070835200000⟩,
  ⟨7, 3, 4, 0, 7, 7, 16005496299420393000131623802773844134747491532800000⟩,
  ⟨7, 3, 5, 0, 8, 7, 301759761450593118266473958845992022745441894400000⟩,
  ⟨7, 3, 0, 1, 2, 7, 95730306282469272732295576742557410237687948902400000⟩,
  ⟨7, 3, 1, 1, 3, 7, -27356290798616028394830284224880998817358623539200000⟩,
  ⟨7, 3, 2, 1, 4, 7, 287476385667805577725705321128757753459445543731200000⟩,
  ⟨7, 3, 3, 1, 5, 7, 59829228055008383147496449202300549532701268377600000⟩,
  ⟨7, 3, 4, 1, 6, 7, 35860863997924660052304787384659123176379462451200000⟩,
  ⟨7, 3, 5, 1, 7, 7, -2393418563283299948485644640773701177649502617600000⟩,
  ⟨7, 3, 6, 1, 8, 7, -218195377831862519042018334340963112288727859200000⟩,
  ⟨7, 3, 0, 2, 1, 7, 98900100054985741924449258215397738650705854464000000⟩,
  ⟨7, 3, 1, 2, 2, 7, -4775814436541999139278775644581655077981048012800000⟩,
  ⟨7, 3, 2, 2, 3, 7, -107140683601775721952573612370506909228269463142400000⟩,
  ⟨7, 3, 3, 2, 4, 7, -77910512510278249608457879954637130559862813491200000⟩,
  ⟨7, 3, 4, 2, 5, 7, -4550555704420362185206269872163823224408873369600000⟩,
  ⟨7, 3, 5, 2, 6, 7, -1672875127658543363328464954040604786175036620800000⟩,
  ⟨7, 3, 6, 2, 7, 7, -291970372346139278042388623035644646217534668800000⟩,
  ⟨7, 3, 7, 2, 8, 7, -195612089731757680062977726275501140074928537600000⟩,
  ⟨7, 3, 0, 3, 0, 7, -552629430325250400458723039083877533461425789337600000⟩,
  ⟨7, 3, 1, 3, 1, 7, 26801966933284834934801583858367049946491781120000000⟩,
  ⟨7, 3, 2, 3, 2, 7, -57291250803256644296100418052585771091867205632000000⟩,
  ⟨7, 3, 3, 3, 3, 7, 104138446339154369974440205553712897020233619865600000⟩,
  ⟨7, 3, 4, 3, 4, 7, 3122135753229870620708030406692192268467149209600000⟩,
  ⟨7, 3, 5, 3, 5, 7, 632112194567624023138278592651049256836136960000000⟩,
  ⟨7, 3, 6, 3, 6, 7, 773636117937801677624070206674511219595096883200000⟩,
  ⟨7, 3, 7, 3, 7, 7, 109225705706738510246943614324995315384870502400000⟩,
  ⟨7, 3, 8, 3, 8, 7, 61782798129918361306018295536592698422067200000000⟩,
  ⟨7, 3, 1, 4, 0, 7, -214456029667141249982071994847294135666365536665600000⟩,
  ⟨7, 3, 2, 4, 1, 7, -132253261695353549496693924598704476227410434457600000⟩,
  ⟨7, 3, 3, 4, 2, 7, -142560809087936633493702226803872725435510947840000000⟩,
  ⟨7, 3, 4, 4, 3, 7, 6978428042768842317221794413047695511736287232000000⟩,
  ⟨7, 3, 5, 4, 4, 7, -2277252336920720740302258506670059688770823782400000⟩,
  ⟨7, 3, 6, 4, 5, 7, -615505867408195696763516643015714040988880076800000⟩,
  ⟨7, 3, 7, 4, 6, 7, -35872489627728958150395316683897960558231552000000⟩,
  ⟨7, 3, 8, 4, 7, 7, 21946884783565318120111511628177513673811558400000⟩,
  ⟨7, 3, 2, 5, 0, 7, 986751524822461543417303677944130608499449344819200000⟩,
  ⟨7, 3, 3, 5, 1, 7, 118385676892184461038503496621027887915790552268800000⟩,
  ⟨7, 3, 4, 5, 2, 7, -47813826712482855631170769196873754028234978099200000⟩,
  ⟨7, 3, 5, 5, 3, 7, 5939205010147154044424382213688130715020741836800000⟩,
  ⟨7, 3, 6, 5, 4, 7, -694217437482760205576246052184834567149138739200000⟩,
  ⟨7, 3, 7, 5, 5, 7, -95006204709767857359442781872901698757433753600000⟩,
  ⟨7, 3, 8, 5, 6, 7, 45699174228412150370382894928189622371064217600000⟩,
  ⟨7, 3, 3, 6, 0, 7, 64472900121862366845482918719233638622823238860800000⟩,
  ⟨7, 3, 4, 6, 1, 7, 25657191532318305209994939957431396435193810124800000⟩,
  ⟨7, 3, 5, 6, 2, 7, 87899786349880071380900025011854830686384947200000⟩,
  ⟨7, 3, 6, 6, 3, 7, 2570540891068015475773585403272653172271952691200000⟩,
  ⟨7, 3, 7, 6, 4, 7, 34010851306354089105102514719243273090839347200000⟩,
  ⟨7, 3, 8, 6, 5, 7, -47959244615816229500423472744130742488085299200000⟩,
  ⟨7, 3, 4, 7, 0, 7, 489570837245332581167915868783662347697532803481600000⟩,
  ⟨7, 3, 5, 7, 1, 7, -4097585590520793684953032695055763135195932262400000⟩,
  ⟨7, 3, 6, 7, 2, 7, -2536809034529520040812255204413368198545329356800000⟩,
  ⟨7, 3, 7, 7, 3, 7, 1425039829797146516591589805615691573777714380800000⟩,
  ⟨7, 3, 8, 7, 4, 7, 94826061348964311915629065303437039473000448000000⟩
]

def collectedFourData_10_3_55 : List CollectedFourTerm := [
  ⟨7, 4, 0, 0, 3, 8, -130284941275600969045107244457989411887768403968000000⟩,
  ⟨7, 4, 1, 0, 4, 8, 1802923682949241149485061621739582852568186880000000⟩,
  ⟨7, 4, 2, 0, 5, 8, -14800886317537165759096932905451634370952560640000000⟩,
  ⟨7, 4, 3, 0, 6, 8, -593924210228275625231420272391334551328129024000000⟩,
  ⟨7, 4, 4, 0, 7, 8, 1704079442299387223237707148487485528210197708800000⟩,
  ⟨7, 4, 5, 0, 8, 8, 26773230290258915132408059852381807498493952000000⟩,
  ⟨7, 4, 0, 1, 2, 8, 50961258523075995984521619583782251530448535552000000⟩,
  ⟨7, 4, 1, 1, 3, 8, -7281450680347477243334487618436954183862059008000000⟩,
  ⟨7, 4, 2, 1, 4, 8, 51011913844951895317728453033635246328766267392000000⟩,
  ⟨7, 4, 3, 1, 5, 8, 7962402076597398958712882641542285024886259712000000⟩,
  ⟨7, 4, 4, 1, 6, 8, 3818048499012841981730972540963408299389301555200000⟩,
  ⟨7, 4, 5, 1, 7, 8, -212352853368278237548630302149026696824619008000000⟩,
  ⟨7, 4, 6, 1, 8, 8, -16593507755631293362498962325325892538073088000000⟩,
  ⟨7, 4, 0, 2, 1, 8, 52648672740987359011434158333796025979602206720000000⟩,
  ⟨7, 4, 1, 2, 2, 8, -1271183200024007815056181546178527380973289472000000⟩,
  ⟨7, 4, 2, 2, 3, 8, -19011827035764448309291489954598017167035203584000000⟩,
  ⟨7, 4, 3, 2, 4, 8, -10368758661406069218474806223312652029860511744000000⟩,
  ⟨7, 4, 4, 2, 5, 8, -484490345183595460140538063208829143410645401600000⟩,
  ⟨7, 4, 5, 2, 6, 8, -148423603015677787902093786766659506839486464000000⟩,
  ⟨7, 4, 6, 2, 7, 8, -22204011313537288319808636964409388231032832000000⟩,
  ⟨7, 4, 7, 2, 8, 8, -13016565315331025743132743229588398938259456000000⟩,
  ⟨7, 4, 0, 3, 0, 8, -294187832045227937384982317694364274789500059648000000⟩,
  ⟨7, 4, 1, 3, 1, 8, 7133905754901924516548849647114995702222028800000000⟩,
  ⟨7, 4, 2, 3, 2, 8, -10166178843720426186819111787441979277831045120000000⟩,
  ⟨7, 4, 3, 3, 3, 8, 13859316062412354490860426583337177163101110272000000⟩,
  ⟨7, 4, 4, 3, 4, 8, 332408770938243360142005833706311513351494041600000⟩,
  ⟨7, 4, 5, 3, 5, 8, 56083307042283865539288590812912871591116800000000⟩,
  ⟨7, 4, 6, 3, 6, 8, 58834137783292649823078539768444025147752448000000⟩,
  ⟨7, 4, 7, 3, 7, 8, 7268178231695799401978452303322774916562944000000⟩,
  ⟨7, 4, 8, 3, 8, 8, 3654397291313939681059165622723237904384000000000⟩,
  ⟨7, 4, 1, 4, 0, 8, -57081971186072647159893689851753549778380652544000000⟩,
  ⟨7, 4, 2, 4, 1, 8, -23467986685741854920973988684356400180327612416000000⟩,
  ⟨7, 4, 3, 4, 2, 8, -18972775000197734782855398540326873691114700800000000⟩,
  ⟨7, 4, 4, 4, 3, 8, 742982007229514695984309888852738932234780672000000⟩,
  ⟨7, 4, 5, 4, 4, 8, -202046160668745132568331960629825567815892992000000⟩,
  ⟨7, 4, 6, 4, 5, 8, -46808513938112508663761949422368979473661952000000⟩,
  ⟨7, 4, 7, 4, 6, 8, -2387053913197173119050667786089144642437120000000⟩,
  ⟨7, 4, 8, 4, 7, 8, 1298138620027991862828725028268185955074048000000⟩,
  ⟨7, 4, 2, 5, 0, 8, 175096412366838267382247450062067432596514537472000000⟩,
  ⟨7, 4, 3, 5, 1, 8, 15755415708506857499618792986665884932380819456000000⟩,
  ⟨7, 4, 4, 5, 2, 8, -5090661210009333527610200988218493820126573363200000⟩,
  ⟨7, 4, 5, 5, 3, 8, 526948002322583190739794549121067971975839744000000⟩,
  ⟨7, 4, 6, 5, 4, 8, -52794438394755492440973134229034653909516288000000⟩,
  ⟨7, 4, 7, 5, 5, 8, -6321973609413530119190375564745907598524416000000⟩,
  ⟨7, 4, 8, 5, 6, 8, 2703065312199284756622304950761713588764672000000⟩,
  ⟨7, 4, 3, 6, 0, 8, 8580407444712127421640663068455433462398058496000000⟩,
  ⟨7, 4, 4, 6, 1, 8, 2731679906667114010883668252445535448419060940800000⟩,
  ⟨7, 4, 5, 6, 2, 8, 7798790703893137123107331794437037386366976000000⟩,
  ⟨7, 4, 6, 6, 3, 8, 195486680955144377663705760376789498035437568000000⟩,
  ⟨7, 4, 7, 6, 4, 8, 2263175389957997788934560563515227983839232000000⟩,
  ⟨7, 4, 8, 6, 5, 8, -2836746455687488025957254114446756412391424000000⟩,
  ⟨7, 4, 4, 7, 0, 8, 52123819448777839283525897452737723767386118553600000⟩,
  ⟨7, 4, 5, 7, 1, 8, -363552788223627313836562318381713368014651392000000⟩,
  ⟨7, 4, 6, 7, 2, 8, -192921412026694921649977904906450137516081152000000⟩,
  ⟨7, 4, 7, 7, 3, 8, 94826061348964311915629065303437039473000448000000⟩,
  ⟨7, 4, 8, 7, 4, 8, 5608876778467180634167936091785328653762560000000⟩
]

def collectedFourData_10_3 : List (List CollectedFourTerm) := [
  collectedFourData_10_3_0,
  collectedFourData_10_3_1,
  collectedFourData_10_3_2,
  collectedFourData_10_3_3,
  collectedFourData_10_3_4,
  collectedFourData_10_3_5,
  collectedFourData_10_3_6,
  collectedFourData_10_3_7,
  collectedFourData_10_3_8,
  collectedFourData_10_3_9,
  collectedFourData_10_3_10,
  collectedFourData_10_3_11,
  collectedFourData_10_3_12,
  collectedFourData_10_3_13,
  collectedFourData_10_3_14,
  collectedFourData_10_3_15,
  collectedFourData_10_3_16,
  collectedFourData_10_3_17,
  collectedFourData_10_3_18,
  collectedFourData_10_3_19,
  collectedFourData_10_3_20,
  collectedFourData_10_3_21,
  collectedFourData_10_3_22,
  collectedFourData_10_3_23,
  collectedFourData_10_3_24,
  collectedFourData_10_3_25,
  collectedFourData_10_3_26,
  collectedFourData_10_3_27,
  collectedFourData_10_3_28,
  collectedFourData_10_3_29,
  collectedFourData_10_3_30,
  collectedFourData_10_3_31,
  collectedFourData_10_3_32,
  collectedFourData_10_3_33,
  collectedFourData_10_3_34,
  collectedFourData_10_3_35,
  collectedFourData_10_3_36,
  collectedFourData_10_3_37,
  collectedFourData_10_3_38,
  collectedFourData_10_3_39,
  collectedFourData_10_3_40,
  collectedFourData_10_3_41,
  collectedFourData_10_3_42,
  collectedFourData_10_3_43,
  collectedFourData_10_3_44,
  collectedFourData_10_3_45,
  collectedFourData_10_3_46,
  collectedFourData_10_3_47,
  collectedFourData_10_3_48,
  collectedFourData_10_3_49,
  collectedFourData_10_3_50,
  collectedFourData_10_3_51,
  collectedFourData_10_3_52,
  collectedFourData_10_3_53,
  collectedFourData_10_3_54,
  collectedFourData_10_3_55
]

def collectedFourData_10_4_0 : List CollectedFourTerm := [
  ⟨0, 4, 6, 2, 8, 0, 16583930293351227691354359490824658918569934848000000⟩,
  ⟨0, 4, 6, 3, 7, 0, 35162368662501569420137650780891221814411264000000⟩,
  ⟨0, 4, 7, 3, 8, 0, -5627721229070855875447475083812689295729229824000000⟩,
  ⟨0, 4, 6, 4, 6, 0, 7105921119476529029727528628806701637345214464000000⟩,
  ⟨0, 4, 7, 4, 7, 0, -14885788875873215619758674354679717233466277888000000⟩,
  ⟨0, 4, 8, 4, 8, 0, 7972410657634949281704532505421344810792386560000000⟩,
  ⟨0, 4, 6, 5, 5, 0, 5936153571300723196221046736154972523459510272000000⟩,
  ⟨0, 4, 7, 5, 6, 0, 4715789059724708735847109524234139484175728640000000⟩,
  ⟨0, 4, 8, 5, 7, 0, -13070785113112568212830828247179421740492128256000000⟩,
  ⟨0, 4, 6, 6, 4, 0, -3957979446604358300870739188555310962785124352000000⟩,
  ⟨0, 4, 7, 6, 5, 0, 29462801208193070475604046074007697413684330496000000⟩,
  ⟨0, 4, 8, 6, 6, 0, 19524308952350274189288260974714358554832142336000000⟩,
  ⟨0, 4, 6, 7, 3, 0, -19980634441716701040968949177977154953212329984000000⟩,
  ⟨0, 4, 7, 7, 4, 0, 22909965838390926595435501683292694034430033920000000⟩,
  ⟨0, 4, 8, 7, 5, 0, 50433356577183599820457658019247344448186613760000000⟩
]

def collectedFourData_10_4_1 : List CollectedFourTerm := [
  ⟨0, 5, 5, 1, 8, 1, 60501914193336028043162039805250183442152292352000000⟩,
  ⟨0, 5, 5, 2, 7, 1, 31012580404290021038670170913750282248006506905600000⟩,
  ⟨0, 5, 6, 2, 8, 1, -54972582611330638325610604320008643660517421875200000⟩,
  ⟨0, 5, 5, 3, 6, 1, -21219271965236456112557198817665658685510542950400000⟩,
  ⟨0, 5, 6, 3, 7, 1, -116556581094916281596952323237876982856915353600000⟩,
  ⟨0, 5, 7, 3, 8, 1, 9327414090213238677753493502676490691950726348800000⟩,
  ⟨0, 5, 5, 4, 5, 1, -12866344534319898122757597459775990012850051481600000⟩,
  ⟨0, 5, 6, 4, 6, 1, -23554780372336282340677729248525363556818459033600000⟩,
  ⟨0, 5, 7, 4, 7, 1, 24671782992293482982645608108962144173336140185600000⟩,
  ⟨0, 5, 8, 4, 8, 1, -8809009600174963130200179011114902670800846848000000⟩,
  ⟨0, 5, 5, 5, 4, 1, -8534717687507329912312851295644753108652995379200000⟩,
  ⟨0, 5, 6, 5, 5, 1, -19677222878988087588293360045151613880634232012800000⟩,
  ⟨0, 5, 7, 5, 6, 1, -7815973025624059531101920082297198928585555968000000⟩,
  ⟨0, 5, 8, 5, 7, 1, 14442390951470328779918186794387521157678812364800000⟩,
  ⟨0, 5, 5, 6, 3, 1, 77773070417951599778783698591811179789533000499200000⟩,
  ⟨0, 5, 6, 6, 4, 1, 13119950955753738088834774798731008163231616204800000⟩,
  ⟨0, 5, 7, 6, 5, 1, -48831798154263489720408566507020962795351126835200000⟩,
  ⟨0, 5, 8, 6, 6, 1, -21573126671959103626602079221993679527313460428800000⟩,
  ⟨0, 5, 5, 7, 2, 1, -4308606266094654153552280053367357242131192217600000⟩,
  ⟨0, 5, 6, 7, 3, 1, 66232012438838527101065134658901439623108073881600000⟩,
  ⟨0, 5, 7, 7, 4, 1, -37971095132335135658844847462431632820749205504000000⟩,
  ⟨0, 5, 8, 7, 5, 1, -55725669604336649241228111388398977262035140608000000⟩
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1014
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1014. -/
namespace LaughlinFock

def collectedFourData_10_4_10 : List CollectedFourTerm := [
  ⟨1, 8, 1, 0, 5, 5, 60501914193336028043162039805250183442152292352000000⟩,
  ⟨1, 8, 2, 0, 6, 5, -51628621673390639913576220328373351692208439296000000⟩,
  ⟨1, 8, 3, 0, 7, 5, 7378368400484534116634264320842591760042426368000000⟩,
  ⟨1, 8, 4, 0, 8, 5, -9492325739652987758808289284880368695966171136000000⟩,
  ⟨1, 8, 1, 1, 4, 5, 26428167080065824136203517721680154152214200320000000⟩,
  ⟨1, 8, 2, 1, 5, 5, 25209615228664859299572750469346449931995447296000000⟩,
  ⟨1, 8, 3, 1, 6, 5, -34986050388925582537660464196147946415294775296000000⟩,
  ⟨1, 8, 4, 1, 7, 5, 11070403317166614303627281605483229324368674816000000⟩,
  ⟨1, 8, 5, 1, 8, 5, 13585270587213470143923347997875748108396134400000000⟩,
  ⟨1, 8, 1, 2, 3, 5, 39918103000438019107304733177328474253734969344000000⟩,
  ⟨1, 8, 2, 2, 4, 5, 92875432767263995720276873175460306426494189568000000⟩,
  ⟨1, 8, 3, 2, 5, 5, -14888289248743820596230117581713988974874198016000000⟩,
  ⟨1, 8, 4, 2, 6, 5, -7298641735732785137495087547292107777968701440000000⟩,
  ⟨1, 8, 5, 2, 7, 5, 6963652340877499630472384765956619329937080320000000⟩,
  ⟨1, 8, 6, 2, 8, 5, -2468739773311604881384486012710116555162124288000000⟩,
  ⟨1, 8, 1, 3, 2, 5, -102861410283456352437830086768323681452896026624000000⟩,
  ⟨1, 8, 2, 3, 3, 5, -105794169029092071682024458744117285422125547520000000⟩,
  ⟨1, 8, 3, 3, 4, 5, 1622208506436923668331448908648566842533609472000000⟩,
  ⟨1, 8, 4, 3, 5, 5, -20025246242932808310427444408887411989173764096000000⟩,
  ⟨1, 8, 5, 3, 6, 5, -4764635221130930602268222430041654204175482880000000⟩,
  ⟨1, 8, 6, 3, 7, 5, -5234388742924556475332870319836850693341184000000⟩,
  ⟨1, 8, 7, 3, 8, 5, 139626925840848243408150309283273888103399424000000⟩,
  ⟨1, 8, 1, 4, 1, 5, 46309064017681046456114668965234218416453189632000000⟩,
  ⟨1, 8, 2, 4, 2, 5, 25225094279440099324909143848593114286606254080000000⟩,
  ⟨1, 8, 3, 4, 3, 5, 23956727530926471020493831619478418553156141056000000⟩,
  ⟨1, 8, 4, 4, 4, 5, 15008236918306526512680873638421078703173795840000000⟩,
  ⟨1, 8, 5, 4, 5, 5, -2889045318607513106100672958784066964443627520000000⟩,
  ⟨1, 8, 6, 4, 6, 5, -1057811374225311284379860645092298533197840384000000⟩,
  ⟨1, 8, 7, 4, 7, 5, 369324786152783401102639039276277703364313088000000⟩,
  ⟨1, 8, 8, 4, 8, 5, -56514282290223733093857845220869761306460160000000⟩,
  ⟨1, 8, 1, 5, 0, 5, 244077079609231979915055779610277066652944171008000000⟩,
  ⟨1, 8, 2, 5, 1, 5, -26125683478872488458130699768515644728945934336000000⟩,
  ⟨1, 8, 3, 5, 2, 5, 29914465189454838283577223052388971339006869504000000⟩,
  ⟨1, 8, 4, 5, 3, 5, 14301107320534812217917598604325921332649787392000000⟩,
  ⟨1, 8, 5, 5, 4, 5, -1916409599864111301937218631942831281002250240000000⟩,
  ⟨1, 8, 6, 5, 5, 5, -883675833335550170404454872882870201910034432000000⟩,
  ⟨1, 8, 7, 5, 6, 5, -117001376315858579908426324743835401993584640000000⟩,
  ⟨1, 8, 8, 5, 7, 5, 92655292277233507847607232731107509577711616000000⟩,
  ⟨1, 8, 2, 6, 0, 5, 470316663465156096785530989132251396418362671104000000⟩,
  ⟨1, 8, 3, 6, 1, 5, 7283033696797920842729685192413257850066829312000000⟩,
  ⟨1, 8, 4, 6, 2, 5, -18113747360254538796105277498001821184569638912000000⟩,
  ⟨1, 8, 5, 6, 3, 5, 17463384755893482128612261092139551168911114240000000⟩,
  ⟨1, 8, 6, 6, 4, 5, 589198164062440571521630483602134731862310912000000⟩,
  ⟨1, 8, 7, 6, 5, 5, -730988652762251638828628392075276903457488896000000⟩,
  ⟨1, 8, 8, 6, 6, 5, -138402593022220827317598570807067418082410496000000⟩,
  ⟨1, 8, 3, 7, 0, 5, -765519969189316444539585714554148181355859542016000000⟩,
  ⟨1, 8, 4, 7, 1, 5, -17400379168788090183217941295122200327777943552000000⟩,
  ⟨1, 8, 5, 7, 2, 5, -967466612570524745566982889058277945738526720000000⟩,
  ⟨1, 8, 6, 7, 3, 5, 2974384604235929493462368599699245482328981504000000⟩,
  ⟨1, 8, 7, 7, 4, 5, -568409125279560188745998664965101545502801920000000⟩,
  ⟨1, 8, 8, 7, 5, 5, -357508547018574127268480955286298199179919360000000⟩
]

def collectedFourData_10_4_11 : List CollectedFourTerm := [
  ⟨2, 2, 6, 2, 8, 0, 10873234397960000254778052118801630273477174886400000⟩,
  ⟨2, 2, 6, 3, 7, 0, 23054165670736371212959468688531252382479155200000⟩,
  ⟨2, 2, 7, 3, 8, 0, -3689808806938585534735573743683292908301267763200000⟩,
  ⟨2, 2, 6, 4, 6, 0, 4658988827061048614331522003208199461745668915200000⟩,
  ⟨2, 2, 7, 4, 7, 0, -9759849974213048450056007351159563334061549158400000⟩,
  ⟨2, 2, 8, 4, 8, 0, 5227101673962838973462422955112380369372971008000000⟩,
  ⟨2, 2, 6, 5, 5, 0, 3892032109476325991482409827541368879615416729600000⟩,
  ⟨2, 2, 7, 5, 6, 0, 3091901552328611662002426075387666735512420352000000⟩,
  ⟨2, 2, 8, 5, 7, 0, -8569844891184692018718584902184580043265330380800000⟩,
  ⟨2, 2, 6, 6, 4, 0, -2595044570495514883121431907350049618189195673600000⟩,
  ⟨2, 2, 7, 6, 5, 0, 19317250970695309308664943216584346666745515212800000⟩,
  ⟨2, 2, 8, 6, 6, 0, 12801090208525834854412858568792379279713029324800000⟩,
  ⟨2, 2, 6, 7, 3, 0, -13100279479095441873560753598913381165916435251200000⟩,
  ⟨2, 2, 7, 7, 4, 0, 15020892165107039258993937220641316627814547456000000⟩,
  ⟨2, 2, 8, 7, 5, 0, 33066570941839223681219829085500708412056403968000000⟩
]

def collectedFourData_10_4_12 : List CollectedFourTerm := [
  ⟨2, 3, 5, 1, 8, 1, 39918103000438019107304733177328474253734969344000000⟩,
  ⟨2, 3, 5, 2, 7, 1, 20461557215063619391270857221223547483731473203200000⟩,
  ⟨2, 3, 6, 2, 8, 1, -36269946895678324476681181913059481939905767014400000⟩,
  ⟨2, 3, 5, 3, 6, 1, -14000103884248872586867008024892347388493876428800000⟩,
  ⟨2, 3, 6, 3, 7, 1, -76901990152871024708332216081946371758961459200000⟩,
  ⟨2, 3, 7, 3, 8, 1, 6154064401847957592222662601342487317439945113600000⟩,
  ⟨2, 3, 5, 4, 5, 1, -8488988707346962183365375832896549654715642675200000⟩,
  ⟨2, 3, 6, 4, 6, 1, -15541031413501632821125139896772157801002906419200000⟩,
  ⟨2, 3, 7, 4, 7, 1, 16278010172433558731834560225322933315093869363200000⟩,
  ⟨2, 3, 8, 4, 8, 1, -5812030201688440413843759987839854127723053056000000⟩,
  ⟨2, 3, 5, 5, 4, 1, -5631057203262884290810744265447080325254899302400000⟩,
  ⟨2, 3, 6, 5, 5, 1, -12982686913607409089858077881436013750073792921600000⟩,
  ⟨2, 3, 7, 5, 6, 1, -5156842067649347929105975495482730103697309696000000⟩,
  ⟨2, 3, 8, 5, 7, 1, 9528836521289545054290437844833470440533498265600000⟩,
  ⟨2, 3, 5, 6, 3, 1, 51313309289411896888020741097679162024250467942400000⟩,
  ⟨2, 3, 6, 6, 4, 1, 8656313781063118514641069251285609235061774745600000⟩,
  ⟨2, 3, 7, 6, 5, 1, -32218364896514157110749211028964036954454124134400000⟩,
  ⟨2, 3, 8, 6, 6, 1, -14233571020263888942636112890486946652753598873600000⟩,
  ⟨2, 3, 5, 7, 2, 1, -2842742928243467431904724492939892054480335667200000⟩,
  ⟨2, 3, 6, 7, 3, 1, 43698721432371729262196874985230474229197255475200000⟩,
  ⟨2, 3, 7, 7, 4, 1, -25052663320509202777487762842074096092250636288000000⟩,
  ⟨2, 3, 8, 7, 5, 1, -36766820499694232482520743840987471701161803776000000⟩
]

def collectedFourData_10_4_13 : List CollectedFourTerm := [
  ⟨2, 4, 4, 0, 8, 2, -16223524135542078322572600067186622484758113812480000⟩,
  ⟨2, 4, 4, 1, 7, 2, 18920648145899315624351251392271809271739323514880000⟩,
  ⟨2, 4, 5, 1, 8, 2, 92875432767263995720276873175460306426494189568000000⟩,
  ⟨2, 4, 4, 2, 6, 2, -12474254845858701662016839992426767117649654579200000⟩,
  ⟨2, 4, 5, 2, 7, 2, 47606871033433477206694793237081921301764269670400000⟩,
  ⟨2, 4, 6, 2, 8, 2, -42193726169112349627529046262282604707397920358400000⟩,
  ⟨2, 4, 4, 3, 5, 2, -34225549633768723299676051099078024779948915425280000⟩,
  ⟨2, 4, 5, 3, 6, 2, -32573334134189691855011069523556073127137614233600000⟩,
  ⟨2, 4, 6, 3, 7, 2, -89461986908964569086801193197143258154873651200000⟩,
  ⟨2, 4, 7, 3, 8, 2, 4772783537943265084709338630385844517062731366400000⟩,
  ⟨2, 4, 4, 4, 4, 2, 25650878462687561006921018404557165849981694771200000⟩,
  ⟨2, 4, 5, 4, 5, 2, -19750900987018717043549456269265970610647230054400000⟩,
  ⟨2, 4, 6, 4, 6, 2, -18079266168569815465043743627425977054969148211200000⟩,
  ⟨2, 4, 7, 4, 7, 2, 12624407856072245301963117424297571071648648396800000⟩,
  ⟨2, 4, 8, 4, 8, 2, -3380639231730897948249124961056516915549175808000000⟩,
  ⟨2, 4, 4, 5, 3, 2, 24442309097175568255629280146027529583832135106560000⟩,
  ⟨2, 4, 5, 5, 4, 2, -13101496197966144140441742156100546311008079052800000⟩,
  ⟨2, 4, 6, 5, 5, 2, -15103080744718156549803481317713346735130646937600000⟩,
  ⟨2, 4, 7, 5, 6, 2, -3999387936346492872804639117992227342966063104000000⟩,
  ⟨2, 4, 8, 5, 7, 2, 5542565585303276306561946498413595740078918860800000⟩,
  ⟨2, 4, 4, 6, 2, 2, -30958568589423915192859968937611675659474734940160000⟩,
  ⟨2, 4, 5, 6, 3, 2, 119388083319548110960095061614763347694450429132800000⟩,
  ⟨2, 4, 6, 6, 4, 2, 10070103889664379283617767212173631726846319001600000⟩,
  ⟨2, 4, 7, 6, 5, 2, -24986947090016984199492497458904830841208805785600000⟩,
  ⟨2, 4, 8, 6, 6, 2, -8279132579998167378316852241270835991590784204800000⟩,
  ⟨2, 4, 4, 7, 1, 2, -29739336718414922624236534188385443088677847695360000⟩,
  ⟨2, 4, 5, 7, 2, 2, -6614066297283572053274539122785007551746827878400000⟩,
  ⟨2, 4, 6, 7, 3, 2, 50835803299108485284508895252178943614739755827200000⟩,
  ⟨2, 4, 7, 7, 4, 2, -19429588523944651023804217633568159465956442112000000⟩,
  ⟨2, 4, 8, 7, 5, 2, -21385875760102788623313647382170028525924384768000000⟩
]

def collectedFourData_10_4_18 : List CollectedFourTerm := [
  ⟨3, 1, 6, 2, 8, 0, 34854581257712886616095235954459580723010679603200000⟩,
  ⟨3, 1, 6, 3, 7, 0, 73901036369657758779214894172932317682178457600000⟩,
  ⟨3, 1, 7, 3, 8, 0, -11827827505585121510985314019824667016289687961600000⟩,
  ⟨3, 1, 6, 4, 6, 0, 14934572244854971008598625161894854506491517337600000⟩,
  ⟨3, 1, 7, 4, 7, 0, -31285583621108940764677262470878266806657823539200000⟩,
  ⟨3, 1, 8, 4, 8, 0, 16755680358702320138160796799708070175209160704000000⟩,
  ⟨3, 1, 6, 5, 5, 0, 12476062269274859506284274943546262343327206604800000⟩,
  ⟨3, 1, 7, 5, 6, 0, 9911212243957977989209490002829879489096318976000000⟩,
  ⟨3, 1, 8, 5, 7, 0, -27470975442397644033993561656602852236229764710400000⟩,
  ⟨3, 1, 6, 6, 4, 0, -8318517613001365499987082083985017768369769676800000⟩,
  ⟨3, 1, 7, 6, 5, 0, 61922209067805443841648023777716281539608077926400000⟩,
  ⟨3, 1, 8, 6, 6, 0, 41034399014159639061234897852045250573057287782400000⟩,
  ⟨3, 1, 6, 7, 3, 0, -41993462008742070100771412308650157726378858905600000⟩,
  ⟨3, 1, 7, 7, 4, 0, 48150061644058024393174795083351756072579760128000000⟩,
  ⟨3, 1, 8, 7, 5, 0, 105996195945384491243429466428082886225044701184000000⟩
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1101. -/
namespace LaughlinFock

def collectedFourData_11_0_0 : List CollectedFourTerm := [

]

def collectedFourData_11_0_1 : List CollectedFourTerm := [

]

def collectedFourData_11_0_2 : List CollectedFourTerm := [

]

def collectedFourData_11_0_9 : List CollectedFourTerm := [

]

def collectedFourData_11_0_10 : List CollectedFourTerm := [

]

def collectedFourData_11_0_17 : List CollectedFourTerm := [

]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1103. -/
namespace LaughlinFock
def collectedFourData_11_1_0 : List CollectedFourTerm := [

]

def collectedFourData_11_1_1 : List CollectedFourTerm := [

]

def collectedFourData_11_1_8 : List CollectedFourTerm := [

]

def collectedFourData_11_1_9 : List CollectedFourTerm := [

]

def collectedFourData_11_1_17 : List CollectedFourTerm := [

]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1105. -/
namespace LaughlinFock

def collectedFourData_11_2_0 : List CollectedFourTerm := [

]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1106
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1106. -/
namespace LaughlinFock

def collectedFourData_11_2_15 : List CollectedFourTerm := [

]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology


def sourceRowI {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : Orbital Q :=
  ⟨rowI b, by have := (rowEntry_bounds b).2.2.1; omega⟩

def sourceRowJ {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : Orbital Q :=
  ⟨rowJ b, by have := (rowEntry_bounds b).2.1; omega⟩

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Rows. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def averagedRowsFour {ι : Type*} [Fintype ι] {Q : ℕ} (hQ : 8 ≤ Q)
    (rows : ι → ComparisonRow) : FockMatrix Q :=
  ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (∑ i,
    rowFourBody Q rowP (sourceRowI hQ) (sourceRowJ hQ) (rows i).alpha)



end LaughlinFock
end

end OAI
end


