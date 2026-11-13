-- Prove2me | Definitions.Def_ApproxDegCompV1_CompositionEstimates
-- name    : ApproxDegCompV1_CompositionEstimates
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:14:59.373317+00:00
-- url     : https://prove2.me/theorems/4971cbda-05b4-4d88-a557-67b3b4f349b0
-- title:
--   Approximate-degree composition: Directed readout, approximation, and composition estimates
-- statement:
--   This module formalizes directed readout, approximation, and composition estimates for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

import Definitions.Def_ApproxDegCompV1_OperatorReadout
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Permutation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

-- NumberGrading.lean
section
/-!
The extreme block diagonal of a nested commutator can only come from
steps in the same direction.  This is the algebraic replacement for
extracting the highest phase harmonic.
-/

namespace ElementaryComposition.NumberGrading

open scoped BigOperators
set_option linter.unusedSectionVars false

variable {X R : Type*} [Fintype X] [DecidableEq X] [Ring R]

def shiftPart (grade : X → ℤ) (q : ℤ) (M : Matrix X X R) : Matrix X X R :=
  fun a b => if grade a - grade b = q then M a b else 0

def UpperShift (grade : X → ℤ) (q : ℤ) (M : Matrix X X R) : Prop :=
  ∀ a b, q < grade a - grade b → M a b = 0

def comm (J T : Matrix X X R) : Matrix X X R := J * T - T * J

def iterComm (J : Matrix X X R) : ℕ → Matrix X X R → Matrix X X R
  | 0, T => T
  | k + 1, T => comm J (iterComm J k T)

theorem upperShift_mul (grade : X → ℤ) {p q : ℤ} {A B : Matrix X X R}
    (hA : UpperShift grade p A) (hB : UpperShift grade q B) :
    UpperShift grade (p + q) (A * B) := by
  intro a c hac
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hab : p < grade a - grade b
  · rw [hA a b hab, zero_mul]
  · have hbc : q < grade b - grade c := by omega
    rw [hB b c hbc, mul_zero]

theorem upperShift_sub (grade : X → ℤ) {q : ℤ} {A B : Matrix X X R}
    (hA : UpperShift grade q A) (hB : UpperShift grade q B) :
    UpperShift grade q (A - B) := by
  intro a b hab
  simp [hA a b hab, hB a b hab]

theorem upperShift_comm (grade : X → ℤ) {p q : ℤ} {A B : Matrix X X R}
    (hA : UpperShift grade p A) (hB : UpperShift grade q B) :
    UpperShift grade (p + q) (comm A B) := by
  apply upperShift_sub grade (upperShift_mul grade hA hB)
  simpa [add_comm] using upperShift_mul grade hB hA

theorem shiftPart_sub (grade : X → ℤ) (q : ℤ) (A B : Matrix X X R) :
    shiftPart grade q (A - B) = shiftPart grade q A - shiftPart grade q B := by
  ext a b
  by_cases h : grade a - grade b = q <;> simp [shiftPart, h]

theorem topShift_mul (grade : X → ℤ) {p q : ℤ} {A B : Matrix X X R}
    (hA : UpperShift grade p A) (hB : UpperShift grade q B) :
    shiftPart grade (p + q) (A * B) = shiftPart grade p A * shiftPart grade q B := by
  ext a c
  simp only [shiftPart, Matrix.mul_apply]
  by_cases hac : grade a - grade c = p + q
  · simp only [hac, if_true]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : grade a - grade b = p
    · have hbc : grade b - grade c = q := by omega
      simp [hab, hbc]
    · by_cases hab' : p < grade a - grade b
      · simp [hab, hA a b hab']
      · have hbc : q < grade b - grade c := by omega
        simp [hab, hB b c hbc]
  · simp only [hac, if_false]
    symm
    apply Finset.sum_eq_zero
    intro b _
    by_cases hab : grade a - grade b = p
    · have hbc : grade b - grade c ≠ q := by omega
      simp [hbc]
    · simp [hab]

theorem topShift_comm (grade : X → ℤ) {p q : ℤ} {A B : Matrix X X R}
    (hA : UpperShift grade p A) (hB : UpperShift grade q B) :
    shiftPart grade (p + q) (comm A B) =
      comm (shiftPart grade p A) (shiftPart grade q B) := by
  rw [comm, shiftPart_sub, topShift_mul grade hA hB]
  have h := topShift_mul grade hB hA
  rw [add_comm q p] at h
  rw [h]
  rfl

theorem upperShift_diagonal (grade : X → ℤ) (p : X → R) :
    UpperShift grade 0 (Matrix.diagonal p) := by
  intro a b h
  have hab : a ≠ b := by intro hab; subst b; simp at h
  simp [hab]

theorem shiftPart_diagonal (grade : X → ℤ) (p : X → R) :
    shiftPart grade 0 (Matrix.diagonal p) = Matrix.diagonal p := by
  ext a b
  by_cases hab : a = b
  · subst b; simp [shiftPart]
  · simp [shiftPart, hab]

theorem upperShift_iterComm (grade : X → ℤ) {J : Matrix X X R}
    (hJ : UpperShift grade 1 J) (p : X → R) (k : ℕ) :
    UpperShift grade (k : ℤ) (iterComm J k (Matrix.diagonal p)) := by
  induction k with
  | zero => exact upperShift_diagonal grade p
  | succ k ih =>
    simpa [iterComm, Nat.cast_add, Nat.cast_one, add_comm] using
      upperShift_comm grade hJ ih

/-- To move up `k` levels in `k` steps, every step must move up one level. -/
theorem topShift_iterComm (grade : X → ℤ) {J : Matrix X X R}
    (hJ : UpperShift grade 1 J) (p : X → R) (k : ℕ) :
    shiftPart grade (k : ℤ) (iterComm J k (Matrix.diagonal p)) =
      iterComm (shiftPart grade 1 J) k (Matrix.diagonal p) := by
  induction k with
  | zero => exact shiftPart_diagonal grade p
  | succ k ih =>
    have h := topShift_comm grade hJ (upperShift_iterComm grade hJ p k)
    rw [ih] at h
    simpa [iterComm, Nat.cast_add, Nat.cast_one, add_comm] using h


section TensorCoordinates

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y]

open ApproxDegree.OperatorGrading

def outputCount (g : Y → Bool) (a : ι → Y) : ℤ :=
  ∑ i, if g (a i) then 1 else 0

theorem outputCount_sub_local (g : Y → Bool) (a b : ι → Y) (i : ι)
    (h : ∀ j, j ≠ i → a j = b j) :
    outputCount g a - outputCount g b =
      (if g (a i) then 1 else 0) - (if g (b i) then 1 else 0) := by
  unfold outputCount
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [h j hji, sub_self]
  · simp

theorem upperShift_localLift (g : Y → Bool) (K : Matrix Y Y R) (i : ι) :
    UpperShift (outputCount g) 1 (localLift K i) := by
  intro a b hab
  by_cases h : ∀ j, j ≠ i → a j = b j
  · rw [outputCount_sub_local g a b i h] at hab
    split at hab <;> split at hab <;> norm_num at hab
  · simp [localLift, h]

/-- Retain the direction from the false output class to the true class. -/
def upward (g : Y → Bool) (K : Matrix Y Y R) : Matrix Y Y R :=
  fun a b => if g a = true ∧ g b = false then K a b else 0

theorem shiftPart_localLift (g : Y → Bool) (K : Matrix Y Y R) (i : ι) :
    shiftPart (outputCount g) 1 (localLift K i) = localLift (upward g K) i := by
  ext a b
  by_cases h : ∀ j, j ≠ i → a j = b j
  · have hn := outputCount_sub_local g a b i h
    cases ha : g (a i) <;> cases hb : g (b i) <;>
      simp [shiftPart, localLift, upward, hn, ha, hb]
  · simp [shiftPart, localLift, h]

theorem upperShift_sum (grade : X → ℤ) (q : ℤ) (K : ι → Matrix X X R)
    (hK : ∀ i, UpperShift grade q (K i)) :
    UpperShift grade q (∑ i, K i) := by
  intro a b hab
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact hK i a b hab

theorem shiftPart_sum (grade : X → ℤ) (q : ℤ) (K : ι → Matrix X X R) :
    shiftPart grade q (∑ i, K i) = ∑ i, shiftPart grade q (K i) := by
  ext a b
  by_cases h : grade a - grade b = q <;> simp [shiftPart, Matrix.sum_apply, h]

/-- The concrete tensor generator satisfies the extreme-diagonal identity.
No grading-support hypothesis is left to the caller. -/
theorem topShift_local_sum (g : Y → Bool) (K : Matrix Y Y R)
    (p : (ι → Y) → R) (k : ℕ) :
    shiftPart (outputCount g) (k : ℤ)
      (iterComm (∑ i : ι, localLift K i) k (Matrix.diagonal p)) =
    iterComm (∑ i : ι, localLift (upward g K) i) k (Matrix.diagonal p) := by
  rw [topShift_iterComm (outputCount g)
    (upperShift_sum _ _ _ (upperShift_localLift g K))]
  simp_rw [shiftPart_sum, shiftPart_localLift]

theorem outputCount_sub_le_distance (g : Y → Bool) (a b : ι → Y) :
    outputCount g a - outputCount g b ≤
      ((gradeOf (fun a j => g (a j)) a b).card : ℤ) := by
  unfold outputCount
  rw [← Finset.sum_sub_distrib]
  have hcard : ((gradeOf (fun a j => g (a j)) a b).card : ℤ) =
      ∑ i : ι, if g (a i) ≠ g (b i) then (1 : ℤ) else 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, gradeOf, Finset.sum_filter]
  rw [hcard]
  apply Finset.sum_le_sum
  intro i _
  cases ha : g (a i) <;> cases hb : g (b i) <;> norm_num

theorem upward_idempotent (g : Y → Bool) (K : Matrix Y Y R) :
    upward g (upward g K) = upward g K := by
  ext a b
  by_cases h : g a = true ∧ g b = false <;> simp [upward, h]

theorem iterComm_eq_iterate (J T : Matrix X X R) (k : ℕ) :
    iterComm J k T = ((fun T => ApproxDegree.matrixCommutator J T)^[k] T) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterComm, ih, Function.iterate_succ_apply']; rfl

theorem distancePart_iter_upward (g : Y → Bool) (K : Matrix Y Y R)
    (p : (ι → Y) → R) (k : ℕ) :
    distancePart (fun a j => g (a j)) k
      (iterComm (∑ i : ι, localLift (upward g K) i) k (Matrix.diagonal p)) =
      iterComm (∑ i : ι, localLift (upward g K) i) k (Matrix.diagonal p) := by
  have ht := topShift_local_sum g (upward g K) p k
  rw [upward_idempotent] at ht
  ext a b
  by_cases hd : (gradeOf (fun a j => g (a j)) a b).card = k
  · simp [distancePart, hd]
  · have hz : iterComm (∑ i : ι, localLift (upward g K) i) k
        (Matrix.diagonal p) a b = 0 := by
      by_cases hlt : k < (gradeOf (fun a j => g (a j)) a b).card
      · rw [iterComm_eq_iterate]
        exact iterated_lifted_sum_bandwidth g (fun _ => upward g K) p k a b hlt
      · have hb := outputCount_sub_le_distance g a b
        have hn : outputCount g a - outputCount g b ≠ (k : ℤ) := by omega
        have he := congrFun (congrFun ht a) b
        simpa [shiftPart, hn] using he.symm
    simp [distancePart, hz]

end TensorCoordinates

section Factorial

variable {ι Y S : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Y] [DecidableEq Y] [CommRing S]

open ApproxDegree ApproxDegree.OperatorGrading

theorem innerCrossing_upward (g : Y → Bool) (K : Matrix Y Y S) :
    ApproxDegree.LocalCommutation.innerCrossing g (upward g K) = upward g K := by
  ext a b
  cases ha : g a <;> cases hb : g b <;>
    simp [ApproxDegree.LocalCommutation.innerCrossing, upward, ha, hb]

/-- Repeated crossings vanish; every set of `k` distinct crossings appears `k!` times. -/
theorem iter_upward_factorial (g : Y → Bool) (K : Matrix Y Y S)
    (p : (ι → Y) → S) (k : ℕ) :
    iterComm (∑ i : ι, localLift (upward g K) i) k (Matrix.diagonal p) =
      k.factorial • (∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
        mixedMatrixCommutator (fun i => localLift (upward g K) i)
          s.toList (Matrix.diagonal p)) := by
  rw [← distancePart_iter_upward g K p k, iterComm_eq_iterate]
  rw [LocalCommutation.highest_distance_localLift_factorial_identity]
  simp_rw [innerCrossing_upward]

end Factorial

section Norm

open ApproxDegree.SpectralCommutator

theorem norm_topShift_le (grade : X → ℤ) {J : Matrix X X ℂ}
    (hJ : UpperShift grade 1 J) (p : X → ℂ) (k : ℕ) :
    ‖matrixOp (iterComm (shiftPart grade 1 J) k (Matrix.diagonal p))‖ ≤
      ‖matrixOp (iterComm J k (Matrix.diagonal p))‖ := by
  rw [← topShift_iterComm grade hJ p k]
  exact BlockDiagonal.norm_shiftMask_le grade (k : ℤ) _

end Norm


end ElementaryComposition.NumberGrading
end

-- OrientedReadout.lean
section
/-!
Directed-crossing Fourier readout, with no auxiliary phase in the statements.
`false` denotes + and `true` denotes -. The local matrix E maps + to -.
The balanced reading is the scalar v_z* T v_z for v_z(b)=2^(-n/2) z^b.
The old tensor-factorization lemma is reused at the fixed parameter 1; no
phase averaging, analytic bound, or norm-to-Fourier theorem is used below.
-/

open scoped BigOperators
open Finset

namespace ElementaryComposition.OrientedReadout

open ApproxDegree TensorPhase

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def E : LocalMatrix := fun a b => if a = true ∧ b = false then 1 else 0

def localE (i : ι) : Matrix (Bits ι) (Bits ι) ℂ := TensorPhase.localLift i E

/-- The ordinary signed balanced reading, a linear functional of its matrix. -/
def balancedReading (z : ι → ℂ) : Matrix (Bits ι) (Bits ι) ℂ →ₗ[ℂ] ℂ :=
  TensorPhase.phaseExpectation z 1

def mixedDirected (S : Finset ι) (T : Matrix (Bits ι) (Bits ι) ℂ) :=
  mixedMatrixCommutator localE S.toList T

theorem mixed_directed_tensor (A : ι → LocalMatrix) (word : List ι)
    (hword : word.Nodup) :
    mixedMatrixCommutator localE word (tensorMatrix A) =
      tensorMatrix (fun i => if i ∈ word then matrixCommutator E (A i) else A i) := by
  induction word with
  | nil => simp [mixedMatrixCommutator]
  | cons i word ih =>
    obtain ⟨hin, hn⟩ := List.nodup_cons.mp hword
    change matrixCommutator (localE i)
      (mixedMatrixCommutator localE word (tensorMatrix A)) = _
    rw [ih hn]
    unfold localE
    rw [localLift_commutator]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j; simp [hin]
    · simp [hji]

theorem commutator_E_Z : matrixCommutator E pauliZ = (2 : ℂ) • E := by
  ext a b
  cases a <;> cases b <;>
    norm_num [matrixCommutator, E, pauliZ, Matrix.mul_apply]

theorem commutator_E_twice_Z : matrixCommutator E (matrixCommutator E pauliZ) = 0 := by
  rw [commutator_E_Z, matrixCommutator_smul_right]
  simp [matrixCommutator]

theorem reading_EZ (z : ℂ) :
    localExpectation z 1 (matrixCommutator E pauliZ) = z := by
  rw [commutator_E_Z]
  simp [localExpectation, localBra, localKet, E]
  ring

theorem reading_Eone (z : ℂ) :
    localExpectation z 1 (matrixCommutator E 1) = 0 := by
  simp [matrixCommutator, localExpectation]

/-- A selected set of directed crossings kills every Walsh term except that set. -/
theorem reading_mixed_walsh (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (S T : Finset ι) :
    balancedReading z (mixedDirected S (walshMatrix T)) =
      if S = T then ∏ i ∈ S, z i else 0 := by
  unfold balancedReading mixedDirected walshMatrix
  rw [mixed_directed_tensor _ _ (nodup_toList S), phaseExpectation_tensor]
  simp only [mem_toList]
  have hlocal : ∀ i,
      localExpectation (z i) 1
        (if i ∈ S then matrixCommutator E (if i ∈ T then pauliZ else 1)
          else if i ∈ T then pauliZ else 1) =
      if i ∈ S then (if i ∈ T then z i else 0)
        else if i ∈ T then 0 else 1 := by
    intro i
    by_cases hs : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hs, hT, reading_EZ, reading_Eone,
        localExpectation_Z (hz i) one_ne_zero,
        localExpectation_one (hz i) one_ne_zero]
  simp_rw [hlocal]
  by_cases hST : S = T
  · subst T
    simp only [if_true]
    have hfac : ∀ i, (if i ∈ S then if i ∈ S then z i else 0
        else if i ∈ S then 0 else 1) = if i ∈ S then z i else 1 := by
      intro i
      split_ifs <;> rfl
    simp_rw [hfac]
    exact Fintype.prod_ite_mem S z
  · rw [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) :=
      not_forall.mp (fun h => hST (Finset.ext h))
    apply prod_eq_zero (mem_univ i)
    by_cases hs : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

def directedMap : List ι → Matrix (Bits ι) (Bits ι) ℂ →ₗ[ℂ]
    Matrix (Bits ι) (Bits ι) ℂ
  | [] => LinearMap.id
  | i :: word => (commutatorMap (localE i)).comp (directedMap word)

theorem directedMap_apply (word : List ι) (T : Matrix (Bits ι) (Bits ι) ℂ) :
    directedMap word T = mixedMatrixCommutator localE word T := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    change matrixCommutator (localE i) (directedMap word T) = _
    rw [ih]
    rfl

/-- Differences on S and averages off S select precisely the coefficient of S. -/
theorem reading_mixed_fourier (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (c : Finset ι → ℂ) (S : Finset ι) :
    balancedReading z (mixedDirected S (fourierMatrix c)) = c S * ∏ i ∈ S, z i := by
  unfold mixedDirected fourierMatrix
  rw [← directedMap_apply, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, directedMap_apply]
  change (∑ T : Finset ι, c T * balancedReading z (mixedDirected S (walshMatrix T))) = _
  simp_rw [reading_mixed_walsh z hz]
  rw [sum_eq_single S]
  · simp
  · intro T hT hTS
    simp [Ne.symm hTS]
  · intro hS
    exact (hS (mem_univ S)).elim

/-- The whole level is read at once, with no loss proportional to its size. -/
theorem reading_whole_level (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (c : Finset ι → ℂ) (k : ℕ) :
    balancedReading z
      (∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
        mixedDirected S (fourierMatrix c)) = fourierLevel k c z := by
  rw [map_sum]
  unfold fourierLevel
  apply sum_congr rfl
  intro S hS
  exact reading_mixed_fourier z hz c S

/-- Scaling and the k! ordering multiplicity give exactly the claimed reading. -/
theorem reading_scaled_factorial (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (c : Finset ι → ℂ) (k : ℕ) (κ : ℂ) :
    balancedReading z
      (((k.factorial : ℂ) * κ ^ k) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          mixedDirected S (fourierMatrix c)) =
      (k.factorial : ℂ) * κ ^ k * fourierLevel k c z := by
  rw [map_smul, reading_whole_level z hz]
  rfl

variable {X : Type*} [Fintype X]

/-- Safe transport from actual raw operators needs both intertwinings, not
invariance of the polynomial multiplier. The crossed blocks are distinct. -/
theorem compressed_mixed_reading
    (W : Matrix (Bits ι) X ℂ) (V : Matrix X (Bits ι) ℂ)
    (A : ι → Matrix X X ℂ) (κ : ℂ)
    (hleft : ∀ i, W * A i = (κ • localE i) * W)
    (hright : ∀ i, A i * V = V * (κ • localE i))
    (P : Matrix X X ℂ) (c : Finset ι → ℂ)
    (hQ : W * P * V = fourierMatrix c)
    (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) (S : Finset ι) :
    balancedReading z (W * mixedMatrixCommutator A S.toList P * V) =
      κ ^ S.card * (c S * ∏ i ∈ S, z i) := by
  rw [compress_mixed_commutators W V A (fun i => κ • localE i)
    hleft hright, hQ, mixedMatrixCommutator_smul, map_smul]
  simp only [length_toList, smul_eq_mul]
  rw [show mixedMatrixCommutator localE S.toList (fourierMatrix c) =
    mixedDirected S (fourierMatrix c) from rfl, reading_mixed_fourier z hz]

section ActualCrossings

variable [DecidableEq X]

/-- Retain exactly the physical crossings from output + to output -. -/
def forward (g : X → Bool) (L : Matrix X X ℂ) : Matrix X X ℂ :=
  fun x y => if g x = true ∧ g y = false then L x y else 0

theorem oneBlock_forward_right (g : X → Bool) (L : Matrix X X ℂ)
    (u : Bool → X → ℂ) (κ : ℂ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = κ * u (!b) x) :
    forward g L * FiberIntertwining.oneBlockV u =
      FiberIntertwining.oneBlockV u * (κ • E) := by
  have hzero : ∀ b x, g x ≠ b → u b x = 0 := by
    intro b x h
    by_contra hu
    exact h (hsupport b x hu)
  ext x b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  cases b with
  | false =>
    change (∑ y, forward g L x y * u false y) = _
    simp only [FiberIntertwining.oneBlockV, Matrix.smul_apply, smul_eq_mul,
      E, Bool.false_eq_true, if_false, mul_zero, and_true,
      Fintype.sum_bool, if_true, mul_one, add_zero]
    by_cases hx : g x = true
    · calc
        (∑ y, forward g L x y * u false y) = ∑ y, L x y * u false y := by
          apply sum_congr rfl
          intro y hy
          by_cases hzeroY : u false y = 0
          · simp [hzeroY]
          · simp [forward, hx, hsupport false y hzeroY]
        _ = κ * u true x := hexchange false x
        _ = u true x * κ := mul_comm _ _
    · have hux : u true x = 0 := hzero true x hx
      simp [forward, hx, hux]
  | true =>
    change (∑ y, forward g L x y * u true y) = _
    simp only [FiberIntertwining.oneBlockV, Matrix.smul_apply, smul_eq_mul,
      E, Bool.true_eq_false, and_false, if_false, mul_zero, Fintype.sum_bool, add_zero]
    apply sum_eq_zero
    intro y hy
    by_cases hu : u true y = 0
    · simp [hu]
    · simp [forward, hsupport true y hu]

/-- The right directed intertwining tensorizes to the actual product vectors. -/
theorem product_forward_right (g : X → Bool) (L : Matrix X X ℂ)
    (u : Bool → X → ℂ) (κ : ℂ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = κ * u (!b) x) (i : ι) :
    OperatorGrading.localLift (forward g L) i * FiberChannel.productV u =
      FiberChannel.productV u * (κ • localE i) := by
  have h := FiberIntertwining.tensorize_intertwining (forward g L)
    (FiberIntertwining.oneBlockV u) (κ • E)
    (oneBlock_forward_right g L u κ hsupport hexchange) i
  have he : OperatorGrading.localLift E i = localE i := by
    rw [FiberIntertwining.localLift_eq_tensorRect]
    rfl
  rw [FiberIntertwining.localLift_smul, he] at h
  exact h

theorem oneBlock_forward_left (g : X → Bool) (L : Matrix X X ℂ)
    (hL : L.IsHermitian) (u : Bool → X → ℂ) (κ : ℝ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = (κ : ℂ) * u (!b) x) :
    (FiberIntertwining.oneBlockV u).conjTranspose * forward g L =
      ((κ : ℂ) • E) * (FiberIntertwining.oneBlockV u).conjTranspose := by
  let W := (FiberIntertwining.oneBlockV u).conjTranspose
  have hfull : W * L = ((κ : ℂ) • pauliX) * W := by
    have h := congrArg Matrix.conjTranspose
      (FiberIntertwining.oneBlock_exchange L u (κ : ℂ) hexchange)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
      hL.eq, FiberIntertwining.pauliX_isHermitian.eq,
      Complex.star_def, Complex.conj_ofReal] using h
  have hW : ∀ b x, W b x ≠ 0 → g x = b := by
    intro b x h
    apply hsupport b x
    intro hu
    apply h
    simp [W, FiberIntertwining.oneBlockV, hu]
  have hrow : ∀ b y, (∑ x, W b x * L x y) = (κ : ℂ) * W (!b) y := by
    intro b y
    have he := congrFun (congrFun hfull b) y
    cases b <;> simpa [Matrix.mul_apply, pauliX] using he
  change W * forward g L = ((κ : ℂ) • E) * W
  ext b y
  rw [Matrix.mul_apply, Matrix.mul_apply]
  cases b with
  | false =>
    simp only [Matrix.smul_apply, smul_eq_mul, E, Bool.false_eq_true,
      false_and, if_false, mul_zero, zero_mul, Fintype.sum_bool, add_zero]
    apply sum_eq_zero
    intro x hx
    by_cases hw : W false x = 0
    · simp [hw]
    · simp [forward, hW false x hw]
  | true =>
    simp only [Matrix.smul_apply, smul_eq_mul, E, true_and,
      Bool.true_eq_false, if_false, if_true, mul_zero, mul_one, zero_mul,
      Fintype.sum_bool, zero_add]
    by_cases hy : g y = false
    · calc
        (∑ x, W true x * forward g L x y) = ∑ x, W true x * L x y := by
          apply sum_congr rfl
          intro x hx
          by_cases hw : W true x = 0
          · simp [hw]
          · simp [forward, hy, hW true x hw]
        _ = (κ : ℂ) * W false y := hrow true y
    · have hw : W false y = 0 := by
        by_contra hw
        exact hy (hW false y hw)
      simp [forward, hy, hw]

/-- Both singular-pair equations give the left product intertwining too. -/
theorem product_forward_left (g : X → Bool) (L : Matrix X X ℂ)
    (hL : L.IsHermitian) (u : Bool → X → ℂ) (κ : ℝ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = (κ : ℂ) * u (!b) x) (i : ι) :
    FiberChannel.productW u * OperatorGrading.localLift (forward g L) i =
      ((κ : ℂ) • localE i) * FiberChannel.productW u := by
  have h := oneBlock_forward_left g L hL u κ hsupport hexchange
  have he : OperatorGrading.localLift E i = localE i := by
    rw [FiberIntertwining.localLift_eq_tensorRect]
    rfl
  have hprod : FiberChannel.productW (ι := ι) u =
      FiberIntertwining.tensorRect
        (fun _ : ι => (FiberIntertwining.oneBlockV u).conjTranspose) := by
    ext a x
    simp [FiberChannel.productW, FiberChannel.productV,
      FiberIntertwining.tensorRect, FiberIntertwining.oneBlockV,
      Matrix.conjTranspose_apply]
  rw [hprod, ← he, ← FiberIntertwining.localLift_smul]
  rw [FiberIntertwining.localLift_eq_tensorRect,
    FiberIntertwining.localLift_eq_tensorRect,
    FiberIntertwining.tensorRect_mul, FiberIntertwining.tensorRect_mul]
  congr 1
  funext j
  by_cases hji : j = i
  · simp only [if_pos hji, h]
  · simp only [if_neg hji, Matrix.one_mul, Matrix.mul_one]

theorem forward_innerCrossing (g : X → Bool) (K : Matrix X X ℂ) :
    forward g (LocalCommutation.innerCrossing g K) = NumberGrading.upward g K := by
  ext x y
  cases hx : g x <;> cases hy : g y <;>
    simp [forward, LocalCommutation.innerCrossing, NumberGrading.upward, hx, hy]

/-- The literal physical forward-commutator reading, for every level k. -/
theorem physical_iterated_reading (g : X → Bool) (K : Matrix X X ℂ)
    (hK : K.IsHermitian) (u : Bool → X → ℂ) (κ : ℝ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hexchange : ∀ b x,
      ∑ y, LocalCommutation.innerCrossing g K x y * u b y = (κ : ℂ) * u (!b) x)
    (p : (ι → X) → ℂ) (k : ℕ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    balancedReading z
      (FiberChannel.productW u *
        NumberGrading.iterComm
          (∑ i : ι, OperatorGrading.localLift (NumberGrading.upward g K) i)
          k (Matrix.diagonal p) * FiberChannel.productV u) =
      (k.factorial : ℂ) * (κ : ℂ) ^ k *
        fourierLevel k (WalshReconstruction.coefficient (FiberChannel.channelQ u p)) z := by
  have hleft : ∀ i : ι, FiberChannel.productW u *
      OperatorGrading.localLift (NumberGrading.upward g K) i =
      ((κ : ℂ) • localE i) * FiberChannel.productW u := by
    intro i
    simpa only [forward_innerCrossing] using
      product_forward_left g (LocalCommutation.innerCrossing g K)
        (FiberIntertwining.innerCrossing_isHermitian g K hK) u κ hsupport hexchange i
  have hright : ∀ i : ι, OperatorGrading.localLift (NumberGrading.upward g K) i *
      FiberChannel.productV u = FiberChannel.productV u * ((κ : ℂ) • localE i) := by
    intro i
    simpa only [forward_innerCrossing] using
      product_forward_right g (LocalCommutation.innerCrossing g K)
        u (κ : ℂ) hsupport hexchange i
  have hQ := WalshReconstruction.channel_compression g u hsupport p
  have hread := compressed_mixed_reading (FiberChannel.productW (ι := ι) u)
    (FiberChannel.productV u)
    (fun i => OperatorGrading.localLift (NumberGrading.upward g K) i)
    (κ : ℂ) hleft hright (Matrix.diagonal p)
    (WalshReconstruction.coefficient (FiberChannel.channelQ u p)) hQ z hz
  rw [NumberGrading.iter_upward_factorial, FiberCompression.factorial_sum_conventions]
  change balancedReading z (FiberCompression.compressionMap
    (FiberChannel.productW u) (FiberChannel.productV u)
    ((k.factorial : ℂ) • _)) = _
  rw [map_smul, map_smul, map_sum, map_sum]
  simp only [smul_eq_mul]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun q : ℂ => (k.factorial : ℂ) * q)
  unfold fourierLevel
  rw [mul_sum]
  apply sum_congr rfl
  intro S hS
  simp only [FiberCompression.compressionMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hread S, (mem_filter.mp hS).2]

/-- The balanced reading is a unit-vector test because the fiber vectors are
normalized and have disjoint supports. This invokes no Fourier extraction. -/
theorem norm_physical_reading_le (g : X → Bool) (u : Bool → X → ℂ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hnorm : ∀ b, ∑ x, ‖u b x‖ ^ 2 = 1)
    (R : Matrix (ι → X) (ι → X) ℂ)
    (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    ‖balancedReading z (FiberChannel.productW u * R * FiberChannel.productV u)‖ ≤
      ‖HilbertPointBridge.matrixOperator R‖ :=
  PhaseHilbertBridge.norm_channel_phaseExpectation_le g u hsupport hnorm R z hz 1 norm_one

/-- Actual forward reading gives the claimed lower bound on the selected operator. -/
theorem physical_directed_lower (g : X → Bool) (K : Matrix X X ℂ)
    (hK : K.IsHermitian) (u : Bool → X → ℂ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hnorm : ∀ b, ∑ x, ‖u b x‖ ^ 2 = 1)
    (hexchange : ∀ b x,
      ∑ y, LocalCommutation.innerCrossing g K x y * u b y = (κ : ℂ) * u (!b) x)
    (p : (ι → X) → ℂ) (k : ℕ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    (k.factorial : ℝ) * κ ^ k *
        ‖fourierLevel k (WalshReconstruction.coefficient (FiberChannel.channelQ u p)) z‖ ≤
      ‖HilbertPointBridge.matrixOperator
        (NumberGrading.iterComm
          (∑ i : ι, OperatorGrading.localLift (NumberGrading.upward g K) i)
          k (Matrix.diagonal p))‖ := by
  have h := norm_physical_reading_le g u hsupport hnorm
    (NumberGrading.iterComm
      (∑ i : ι, OperatorGrading.localLift (NumberGrading.upward g K) i)
      k (Matrix.diagonal p)) z hz
  rw [physical_iterated_reading g K hK u κ hsupport hexchange p k z hz] at h
  simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
    using h

/-- The actual full J-commutator dominates the directed Fourier reading, with
the extreme block diagonal providing the bridge. No phase filter is used. -/
theorem physical_fourier_lower (g : X → Bool) (K : Matrix X X ℂ)
    (hK : K.IsHermitian) (u : Bool → X → ℂ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hsupport : ∀ b x, u b x ≠ 0 → g x = b)
    (hnorm : ∀ b, ∑ x, ‖u b x‖ ^ 2 = 1)
    (hexchange : ∀ b x,
      ∑ y, LocalCommutation.innerCrossing g K x y * u b y = (κ : ℂ) * u (!b) x)
    (p : (ι → X) → ℂ) (k : ℕ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    (k.factorial : ℝ) * κ ^ k *
        ‖fourierLevel k (WalshReconstruction.coefficient (FiberChannel.channelQ u p)) z‖ ≤
      ‖HilbertPointBridge.matrixOperator
        (OperatorExtraction.rawCommutator
          (fun i => OperatorGrading.localLift K i) p k)‖ := by
  apply (physical_directed_lower g K hK u κ hκ hsupport hnorm hexchange p k z hz).trans
  rw [← NumberGrading.topShift_local_sum g K p k]
  have h := BlockDiagonal.norm_shiftMask_le (NumberGrading.outputCount g) (k : ℤ)
    (NumberGrading.iterComm (∑ i : ι, OperatorGrading.localLift K i)
      k (Matrix.diagonal p))
  have he : NumberGrading.iterComm (∑ i : ι, OperatorGrading.localLift K i)
      k (Matrix.diagonal p) = OperatorExtraction.rawCommutator
        (fun i => OperatorGrading.localLift K i) p k :=
    NumberGrading.iterComm_eq_iterate _ _ _
  rw [← he]
  exact h

/-- Complete norm lower bound for the distributions actually constructed from
inner hardness. It has no distribution, intertwining, or extraction premises. -/
theorem constructed_fourier_lower {σ : Type*} {coords : X → σ → ℝ}
    {g : X → Bool} {d : ℕ} {ε : ℝ}
    (w : ConstructedExtraction.InnerData coords g d ε)
    (p : (ι → X) → ℂ) (k : ℕ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    (k.factorial : ℝ) * ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖ ^ k *
        ‖fourierLevel k (WalshReconstruction.coefficient (FiberChannel.channelQ w.u p)) z‖ ≤
      ‖HilbertPointBridge.matrixOperator
        (OperatorExtraction.rawCommutator
          (fun i => OperatorGrading.localLift
            (DegreeScaleWitness.witnessMatrix w.psi coords d) i) p k)‖ :=
  physical_fourier_lower g (DegreeScaleWitness.witnessMatrix w.psi coords d)
    (DegreeScaleWitness.witnessMatrix_isHermitian w.psi coords d)
    w.u ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖ (norm_nonneg _)
    w.support w.normalized w.exchange p k z hz

end ActualCrossings

end
end ElementaryComposition.OrientedReadout
end

-- RawPolynomialBound.lean
section
/-!
# Elementary raw polynomial bound

The actual tensor polynomial filtration supplies bandwidth. The operator bound
uses only spectral bins and contractive block diagonals, not Bernstein.
-/

namespace ElementaryComposition.RawPolynomialBound

open ApproxDegree
open ApproxDegree.HilbertPointBridge ApproxDegree.TensorFiltrationBandwidth
open scoped BigOperators

noncomputable section
variable {ι Y σ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Y] [DecidableEq Y] [Fintype σ]

/-- The actual raw polynomial commutator satisfies the elementary 3D bound. -/
theorem norm_rawCommutator_le (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hdeg : p.totalDegree ≤ D)
    (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ι → Y,
      |MvPolynomial.eval (ApproxDegree.RawPolynomialBound.productCoords coords x) p| ≤ M)
    (k : ℕ) :
    ‖matrixOperator (OperatorExtraction.rawCommutator
      (fun i => OperatorGrading.localLift (DegreeScaleWitness.witnessMatrix ψ coords d) i)
      (ApproxDegree.RawPolynomialBound.rawEval coords p) k)‖ ≤ (3 * D : ℝ) ^ k * M := by
  rw [ApproxDegree.RawPolynomialBound.matrixOperator_rawCommutator]
  calc
    _ ≤ (3 * D : ℝ) ^ k *
        ‖matrixOperator (Matrix.diagonal (ApproxDegree.RawPolynomialBound.rawEval coords p))‖ :=
      ProjectionBandwidth.norm_iterated_commutator_le_of_generator_eq
        (ApproxDegree.RawPolynomialBound.productLevelOperator d ψ coords)
        (ApproxDegree.RawPolynomialBound.productLevelOperator_resolution d ψ coords)
        energy _ (ApproxDegree.RawPolynomialBound.actual_generator_eq_spectral_sum d ψ coords)
        D _ (ApproxDegree.RawPolynomialBound.actual_polynomial_bandwidth d ψ coords p D hdeg) k
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (ApproxDegree.RawPolynomialBound.norm_polynomial_operator_le coords p M hM hp) (by positivity)

/-- A deliberately loose constant retains the existing end-to-end theorem's
cutoff without making the elementary proof depend on its previous analytic route. -/
theorem two_mul_three_pow_le_seven_pow (D k : ℕ) (hk : 0 < k) :
    2 * (3 * D) ^ k ≤ (7 * D) ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      simp
      omega
    · have hi := ih (by omega)
      rw [pow_succ, pow_succ]
      have hmul := Nat.mul_le_mul_right (3 * D) hi
      have hmore := Nat.mul_le_mul_left ((7 * D) ^ k) (by omega : 3 * D ≤ 7 * D)
      calc
        2 * ((3 * D) ^ k * (3 * D)) = (2 * (3 * D) ^ k) * (3 * D) := by ring
        _ ≤ (7 * D) ^ k * (3 * D) := hmul
        _ ≤ (7 * D) ^ k * (7 * D) := hmore

theorem fourier_bound_arithmetic (q κ M : ℝ) (D k : ℕ)
    (hκ : 0 < κ) (hk : 0 < k) (hM : 0 ≤ M)
    (hq : (k.factorial : ℝ) * κ ^ k * q ≤ (3 * D : ℝ) ^ k * M) :
    q ≤ M / (2 * (k.factorial : ℝ)) * (((7 * D : ℕ) : ℝ) / κ) ^ k := by
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hκk : 0 < κ ^ k := pow_pos hκ k
  have heq : M / (2 * (k.factorial : ℝ)) * (((7 * D : ℕ) : ℝ) / κ) ^ k =
      (7 * D : ℝ) ^ k * M / (2 * (k.factorial : ℝ) * κ ^ k) := by
    push_cast
    rw [div_pow]
    field_simp
  rw [heq]
  apply (le_div_iff₀ (by positivity)).mpr
  have hp : (2 : ℝ) * (3 * D : ℝ) ^ k ≤ (7 * D : ℝ) ^ k := by
    exact_mod_cast two_mul_three_pow_le_seven_pow D k hk
  calc
    q * (2 * (k.factorial : ℝ) * κ ^ k) =
        2 * ((k.factorial : ℝ) * κ ^ k * q) := by ring
    _ ≤ 2 * ((3 * D : ℝ) ^ k * M) := by linarith
    _ = (2 * (3 * D : ℝ) ^ k) * M := by ring
    _ ≤ (7 * D : ℝ) ^ k * M := mul_le_mul_of_nonneg_right hp hM

/-- The exact factor-three Fourier estimate of the elementary argument. -/
theorem fourier_level_bound_three {coords : Y → σ → ℝ} {g : Y → Bool}
    {d : ℕ} {ε : ℝ} (w : ConstructedExtraction.InnerData coords g d ε)
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hdeg : p.totalDegree ≤ D)
    (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ι → Y,
      |MvPolynomial.eval (ApproxDegree.RawPolynomialBound.productCoords coords x) p| ≤ M)
    (k : ℕ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    ‖TensorPhase.fourierLevel k
      (WalshReconstruction.coefficient
        (FiberChannel.channelQ w.u (ApproxDegree.RawPolynomialBound.rawEval coords p))) z‖ ≤
      M / (k.factorial : ℝ) *
        ((3 * D : ℝ) / ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖) ^ k := by
  have hκ := w.scale_pos
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have heq : M / (k.factorial : ℝ) *
      ((3 * D : ℝ) / ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖) ^ k =
      (3 * D : ℝ) ^ k * M /
        ((k.factorial : ℝ) * ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖ ^ k) := by
    rw [div_pow]
    field_simp
  rw [heq]
  apply (le_div_iff₀ (by positivity)).mpr
  have h := (OrientedReadout.constructed_fourier_lower w
    (ApproxDegree.RawPolynomialBound.rawEval coords p) k z hz).trans
      (norm_rawCommutator_le d w.psi coords p D hdeg M hM hp k)
  simpa only [mul_comm] using h


/-- Fourier suppression for the channel constructed from inner hardness.
Every input is an actual polynomial-degree or pointwise-bound hypothesis.
The proof uses directed differences, one block diagonal, and spectral bins. -/
theorem fourier_level_bound {coords : Y → σ → ℝ} {g : Y → Bool} {d : ℕ} {ε : ℝ}
    (w : ConstructedExtraction.InnerData coords g d ε)
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hdeg : p.totalDegree ≤ D)
    (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x : ι → Y,
      |MvPolynomial.eval (ApproxDegree.RawPolynomialBound.productCoords coords x) p| ≤ M)
    {k : ℕ} (hk : 0 < k) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) :
    ‖TensorPhase.fourierLevel k
      (WalshReconstruction.coefficient
        (FiberChannel.channelQ w.u (ApproxDegree.RawPolynomialBound.rawEval coords p))) z‖ ≤
      M / (2 * (k.factorial : ℝ)) *
        (((7 * D : ℕ) : ℝ) / ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖) ^ k := by
  apply fourier_bound_arithmetic _ _ M D k w.scale_pos hk hM
  exact (OrientedReadout.constructed_fourier_lower w
    (ApproxDegree.RawPolynomialBound.rawEval coords p) k z hz).trans
      (norm_rawCommutator_le d w.psi coords p D hdeg M hM hp k)



end
end ElementaryComposition.RawPolynomialBound
end

-- ChannelApproximation.lean
section
/-!
# Approximation preserved by the actual positive exact-fiber channel

Only raw points in the product promise domain are used. The outer target is
an arbitrary real function on the full logical Boolean cube.
-/

open scoped BigOperators
open Finset

namespace ApproxDegree.ChannelApproximation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]

/-- The real form of the actual product channel. -/
def realChannelQ (u : Bool → Y → ℂ) (p : (ι → Y) → ℝ)
    (b : TensorPhase.Bits ι) : ℝ :=
  ∑ x, p x * FiberChannel.weights u b x

/-- The real channel embeds as precisely the previously defined complex channel. -/
theorem complex_channel_eq (u : Bool → Y → ℂ) (p : (ι → Y) → ℝ) :
    FourierTruncation.complexFunction (realChannelQ u p) =
      FiberChannel.channelQ u (fun x => (p x : ℂ)) := by
  funext b
  simp [FourierTruncation.complexFunction, realChannelQ, FiberChannel.channelQ]

/-- The channel error is an actual weighted sum of pointwise errors. -/
theorem realChannelQ_sub (u : Bool → Y → ℂ)
    (hnorm : ∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) (p : (ι → Y) → ℝ)
    (F : TensorPhase.Bits ι → ℝ) (b : TensorPhase.Bits ι) :
    realChannelQ u p b - F b =
      ∑ x, (p x - F b) * FiberChannel.weights u b x := by
  simp only [sub_mul, sum_sub_distrib, ← mul_sum,
    FiberChannel.weights_sum_one u hnorm, mul_one, realChannelQ]

/-- Uniform approximation to any total outer target is preserved by the
normalized positive channel on the exact product fibers. -/
theorem realChannelQ_approximation (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b)
    (hnorm : ∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) (p : (ι → Y) → ℝ)
    (F : TensorPhase.Bits ι → ℝ) (δ : ℝ)
    (happrox : ∀ x, |p x - F (FiberChannel.productLabel g x)| ≤ δ)
    (b : TensorPhase.Bits ι) : |realChannelQ u p b - F b| ≤ δ := by
  rw [realChannelQ_sub u hnorm p F b]
  calc
    |∑ x, (p x - F b) * FiberChannel.weights u b x| ≤
        ∑ x, |(p x - F b) * FiberChannel.weights u b x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, δ * FiberChannel.weights u b x := by
      apply sum_le_sum
      intro x hx
      by_cases hw : FiberChannel.weights u b x = 0
      · simp [hw]
      · have hlabel := FiberChannel.weights_support g u hsupport b x hw
        rw [abs_mul, abs_of_nonneg (FiberChannel.weights_nonnegative u b x)]
        apply mul_le_mul_of_nonneg_right _ (FiberChannel.weights_nonnegative u b x)
        simpa only [hlabel] using happrox x
    _ = δ := by rw [← mul_sum, FiberChannel.weights_sum_one u hnorm, mul_one]

/-- Combining the actual channel with Fourier truncation gives a real outer
polynomial. Neither a real polynomial representation nor a remainder is assumed. -/
theorem exists_outer_approximant_from_channel (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b)
    (hnorm : ∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) (p : (ι → Y) → ℝ)
    (F : TensorPhase.Bits ι → ℝ) (δ : ℝ)
    (happrox : ∀ x, |p x - F (FiberChannel.productLabel g x)| ≤ δ)
    {a : ℝ} (ha : 0 ≤ a) (r : ℕ) (hr : 1 ≤ r)
    (hcut : 8 * Real.exp 1 * a ≤ (r : ℝ))
    (hlevel : ∀ (b : TensorPhase.Bits ι) (k : ℕ), 1 ≤ k →
      ‖TensorPhase.fourierLevel k
        (WalshReconstruction.coefficient (FiberChannel.channelQ u (fun x => (p x : ℂ))))
        (fun i => TensorPhase.bitSign (b i))‖ ≤ a ^ k / (2 * (k.factorial : ℝ))) :
    ∃ q : MvPolynomial ι ℝ, q.totalDegree < r ∧
      ∀ b : TensorPhase.Bits ι,
        |F b - MvPolynomial.eval (fun i => FourierTruncation.realSign (b i)) q| < δ + 1 / 15 := by
  have hlevel' : ∀ (b : TensorPhase.Bits ι) (k : ℕ), 1 ≤ k →
      ‖TensorPhase.fourierLevel k
        (WalshReconstruction.coefficient (FourierTruncation.complexFunction (realChannelQ u p)))
        (fun i => TensorPhase.bitSign (b i))‖ ≤ a ^ k / (2 * (k.factorial : ℝ)) := by
    simpa only [complex_channel_eq] using hlevel
  obtain ⟨q, hdegree, hq⟩ :=
    FourierTruncation.exists_real_approximant (realChannelQ u p) ha r hr hcut hlevel'
  refine ⟨q, hdegree, ?_⟩
  intro b
  have hchannel : |F b - realChannelQ u p b| ≤ δ := by
    rw [abs_sub_comm]
    exact realChannelQ_approximation g u hsupport hnorm p F δ happrox b
  exact (abs_sub_le (F b) (realChannelQ u p b)
    (MvPolynomial.eval (fun i => FourierTruncation.realSign (b i)) q)).trans_lt
      (add_lt_add_of_le_of_lt hchannel (hq b))

end

end ApproxDegree.ChannelApproximation
end

-- CompositionArithmetic.lean
section
/-!
# Final ceiling-cutoff arithmetic for the composition constant

The cutoff uses the exact amplitude `63 D / κ`. No positivity assumption on
the raw degree `D` is made; it is a consequence of the strict cutoff premise.
-/

namespace ApproxDegree.CompositionArithmetic

noncomputable section

def amplitude (D : ℕ) (κ : ℝ) : ℝ := 63 * (D : ℝ) / κ

def cutoff (D : ℕ) (κ : ℝ) : ℕ :=
  max 1 (Nat.ceil (8 * Real.exp 1 * amplitude D κ))

theorem one_le_cutoff (D : ℕ) (κ : ℝ) : 1 ≤ cutoff D κ := le_max_left _ _

theorem threshold_le_cutoff (D : ℕ) (κ : ℝ) :
    8 * Real.exp 1 * amplitude D κ ≤ (cutoff D κ : ℝ) := by
  have h : Nat.ceil (8 * Real.exp 1 * amplitude D κ) ≤ cutoff D κ := le_max_right _ _
  exact (Nat.le_ceil _).trans (by exact_mod_cast h)

/-- A positive natural degree below this maximum is below the unrounded
real threshold; no additive rounding loss is incurred. -/
theorem lt_threshold_of_lt_max_ceil {df : ℕ} (hdf : 0 < df) {x : ℝ}
    (hcut : df < max 1 (Nat.ceil x)) : (df : ℝ) < x := by
  have hc : df < Nat.ceil x := by omega
  exact Nat.lt_ceil.mp hc

theorem amplitude_nonnegative (D : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ amplitude D κ := by
  unfold amplitude
  positivity

/-- The strict cutoff implication is slightly stronger than the required
composition lower bound. In particular, `D > 0` is not a premise. -/
theorem product_lt_of_lt_cutoff {df dg D : ℕ} (hdf : 0 < df) (hdg : 0 < dg)
    {κ : ℝ} (hκ : (dg : ℝ) / 3 < κ) (hcut : df < cutoff D κ) :
    (df : ℝ) * (dg : ℝ) / (1512 * Real.exp 1) < (D : ℝ) := by
  have hdfR : 0 < (df : ℝ) := by exact_mod_cast hdf
  have hdgR : 0 < (dg : ℝ) := by exact_mod_cast hdg
  have hκpos : 0 < κ := (div_pos hdgR (by norm_num)).trans hκ
  have hthreshold : (df : ℝ) < 8 * Real.exp 1 * amplitude D κ :=
    lt_threshold_of_lt_max_ceil hdf hcut
  have hdiv : (df : ℝ) < (504 * Real.exp 1 * (D : ℝ)) / κ := by
    convert hthreshold using 1
    unfold amplitude
    ring
  have hmul : (df : ℝ) * κ < 504 * Real.exp 1 * (D : ℝ) :=
    (lt_div_iff₀ hκpos).mp hdiv
  have hscale : (df : ℝ) * ((dg : ℝ) / 3) < (df : ℝ) * κ :=
    mul_lt_mul_of_pos_left hκ hdfR
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 1512 * Real.exp 1)).mpr
  nlinarith

/-- The requested non-strict lower bound with the exact constant `1512 e`. -/
theorem product_le_of_lt_cutoff {df dg D : ℕ} (hdf : 0 < df) (hdg : 0 < dg)
    {κ : ℝ} (hκ : (dg : ℝ) / 3 < κ) (hcut : df < cutoff D κ) :
    (df : ℝ) * (dg : ℝ) / (1512 * Real.exp 1) ≤ (D : ℝ) :=
  (product_lt_of_lt_cutoff hdf hdg hκ hcut).le

/-- Explicit expanded-cutoff interface matching the final theorem calculation. -/
theorem product_le_of_explicit_cutoff {df dg D : ℕ} (hdf : 0 < df) (hdg : 0 < dg)
    {κ : ℝ} (hκ : (dg : ℝ) / 3 < κ)
    (hcut : df < max 1 (Nat.ceil (8 * Real.exp 1 * (63 * (D : ℝ) / κ)))) :
    (df : ℝ) * (dg : ℝ) / (1512 * Real.exp 1) ≤ (D : ℝ) :=
  product_le_of_lt_cutoff hdf hdg hκ hcut

/-- Positive raw degree follows from the hypotheses rather than being assumed. -/
theorem degree_pos_of_lt_cutoff {df dg D : ℕ} (hdf : 0 < df) (hdg : 0 < dg)
    {κ : ℝ} (hκ : (dg : ℝ) / 3 < κ) (hcut : df < cutoff D κ) : 0 < D := by
  have hdfR : 0 < (df : ℝ) := by exact_mod_cast hdf
  have hdgR : 0 < (dg : ℝ) := by exact_mod_cast hdg
  have hlower : (0 : ℝ) < (df : ℝ) * (dg : ℝ) / (1512 * Real.exp 1) := by positivity
  have hD := hlower.trans (product_lt_of_lt_cutoff hdf hdg hκ hcut)
  exact_mod_cast hD

end

end ApproxDegree.CompositionArithmetic
end


