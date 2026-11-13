-- Prove2me | Definitions.Def_ApproxDegCompV1_SpectralGrading
-- name    : ApproxDegCompV1_SpectralGrading
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:07:40.03234+00:00
-- url     : https://prove2.me/theorems/5256712c-7056-42a9-9c18-9093b23f8baf
-- title:
--   Approximate-degree composition: Degree grading and the inner hardness witness
-- statement:
--   This module formalizes degree grading and the inner hardness witness for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

import Definitions.Def_ApproxDegCompV1_DualWitness
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

-- OperatorGrading.lean
section
/-!
# Actual logical grading of finite matrices

Rows and columns are points of an arbitrary finite type `X`, equipped with
Boolean logical labels.  Grade means the actual set of differing label bits;
it is not an abstract grading supplied as a hypothesis.
-/

namespace ApproxDegree.OperatorGrading

set_option linter.unusedSectionVars false

open scoped BigOperators symmDiff
open ProtectedCrossings

variable {ι X R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype X] [DecidableEq X] [Ring R]

/-- The actual set of differing logical bits of two point indices. -/
def gradeOf (label : X → ι → Bool) (a b : X) : Finset ι :=
  Finset.univ.filter (fun i => label a i ≠ label b i)

@[simp] theorem mem_gradeOf (label : X → ι → Bool) (a b : X) (i : ι) :
    i ∈ gradeOf label a b ↔ label a i ≠ label b i := by
  simp [gradeOf]

@[simp] theorem gradeOf_self (label : X → ι → Bool) (a : X) :
    gradeOf label a a = ∅ := by
  simp [gradeOf]

/-- Logical differences compose by symmetric difference. -/
theorem gradeOf_comp (label : X → ι → Bool) (a b c : X) :
    gradeOf label a c = gradeOf label a b ∆ gradeOf label b c := by
  ext i
  simp only [mem_gradeOf, Finset.mem_symmDiff]
  cases h₁ : label a i <;> cases h₂ : label b i <;> cases h₃ : label c i <;> simp

/-- A matrix has grade `s` if all entries outside exactly that grade vanish. -/
def HasGrade (label : X → ι → Bool) (s : Finset ι) (A : Matrix X X R) : Prop :=
  ∀ a b, gradeOf label a b ≠ s → A a b = 0

/-- The actual entry mask selecting one logical grade. -/
def gradePart (label : X → ι → Bool) (s : Finset ι) (A : Matrix X X R) :
    Matrix X X R := fun a b => if gradeOf label a b = s then A a b else 0

/-- The actual entry mask selecting logical Hamming distance `k`. -/
def distancePart (label : X → ι → Bool) (k : ℕ) (A : Matrix X X R) :
    Matrix X X R := fun a b => if (gradeOf label a b).card = k then A a b else 0

theorem hasGrade_gradePart (label : X → ι → Bool) (s : Finset ι)
    (A : Matrix X X R) : HasGrade label s (gradePart label s A) := by
  intro a b h
  simp [gradePart, h]

theorem hasGrade_sub (label : X → ι → Bool) (s : Finset ι)
    {A B : Matrix X X R} (hA : HasGrade label s A) (hB : HasGrade label s B) :
    HasGrade label s (A - B) := by
  intro a b h
  simp [hA a b h, hB a b h]

/-- Matrix multiplication adds actual logical grades by symmetric difference. -/
theorem hasGrade_mul (label : X → ι → Bool) (s t : Finset ι)
    {A B : Matrix X X R} (hA : HasGrade label s A) (hB : HasGrade label t B) :
    HasGrade label (s ∆ t) (A * B) := by
  intro a c hac
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hab : gradeOf label a b = s
  · by_cases hbc : gradeOf label b c = t
    · exact False.elim (hac (by rw [gradeOf_comp label a b c, hab, hbc]))
    · rw [hB b c hbc, mul_zero]
  · rw [hA a b hab, zero_mul]

/-- The same exact propagation law holds for a commutator. -/
theorem hasGrade_commutator (label : X → ι → Bool) (s t : Finset ι)
    {A B : Matrix X X R} (hA : HasGrade label s A) (hB : HasGrade label t B) :
    HasGrade label (s ∆ t) (matrixCommutator A B) := by
  apply hasGrade_sub label (s ∆ t) (hasGrade_mul label s t hA hB)
  simpa [symmDiff_comm] using hasGrade_mul label t s hB hA

/-- Point multiplication starts at grade zero, for any label map. -/
theorem hasGrade_diagonal (label : X → ι → Bool) (p : X → R) :
    HasGrade label ∅ (Matrix.diagonal p) := by
  intro a b hab
  have hne : a ≠ b := by
    intro h
    subst b
    exact hab (gradeOf_self label a)
  simp [hne]

/-- A homogeneous matrix survives exactly its own Hamming-distance mask. -/
theorem distancePart_of_hasGrade (label : X → ι → Bool) (s : Finset ι)
    {A : Matrix X X R} (hA : HasGrade label s A) (k : ℕ) :
    distancePart label k A = if s.card = k then A else 0 := by
  by_cases hk : s.card = k
  · simp only [hk, if_true]
    ext a b
    by_cases h : gradeOf label a b = s
    · simp [distancePart, h, hk]
    · simp [distancePart, hA a b h]
  · simp only [hk, if_false]
    ext a b
    by_cases h : gradeOf label a b = s
    · simp [distancePart, h, hk]
    · simp [distancePart, hA a b h]

/-- A local matrix can preserve its logical bit or change only that bit. -/
def LocalAt (label : X → ι → Bool) (i : ι) (A : Matrix X X R) : Prop :=
  ∀ a b, gradeOf label a b ≠ ∅ → gradeOf label a b ≠ {i} → A a b = 0

/-- Every genuinely local matrix splits into its actual even and odd masks. -/
theorem local_split (label : X → ι → Bool) (i : ι) {A : Matrix X X R}
    (hA : LocalAt label i A) :
    A = gradePart label ∅ A + gradePart label {i} A := by
  ext a b
  by_cases h₀ : gradeOf label a b = ∅
  · simp [gradePart, h₀]
  · by_cases h₁ : gradeOf label a b = {i}
    · simp [gradePart, h₁]
    · simp [gradePart, h₀, h₁, hA a b h₀ h₁]

/-- Summing the actual grade masks recovers every matrix. -/
theorem sum_gradeParts (label : X → ι → Bool) (A : Matrix X X R) :
    (∑ s : Finset ι, gradePart label s A) = A := by
  ext a b
  simp [Matrix.sum_apply, gradePart]

theorem singleton_symmDiff_toggle (i : ι) (s : Finset ι) :
    ({i} : Finset ι) ∆ s = toggle i s := by
  ext j
  by_cases hi : i ∈ s <;> by_cases hji : j = i <;>
    simp_all [toggle, Finset.mem_symmDiff]

/-- Each expanded local step remembers its block and whether it is odd. -/
def stepParity (step : ι × Bool) : Option ι :=
  if step.2 then some step.1 else none

/-- Even and odd local parts are actual entry masks of the original operator. -/
def localPart (label : X → ι → Bool) (H : ι → Matrix X X R)
    (step : ι × Bool) : Matrix X X R :=
  if step.2 then gradePart label {step.1} (H step.1)
  else gradePart label ∅ (H step.1)

/-- Every arbitrary expanded commutator word has its actual parity support.
This derives operator support from concrete matrix multiplication. -/
theorem hasGrade_mixed_localParts (label : X → ι → Bool)
    (H : ι → Matrix X X R) (w : List (ι × Bool))
    {P : Matrix X X R} (hP : HasGrade label ∅ P) :
    HasGrade label (paritySupport (w.map stepParity))
      (mixedMatrixCommutator (localPart label H) w P) := by
  induction w with
  | nil => simpa [mixedMatrixCommutator, paritySupport] using hP
  | cons step w ih =>
    obtain ⟨i, b⟩ := step
    cases b with
    | false =>
      simpa [mixedMatrixCommutator, localPart, stepParity, paritySupport,
        ← Finset.bot_eq_empty, bot_symmDiff] using
        hasGrade_commutator label ∅ (paritySupport (w.map stepParity))
          (hasGrade_gradePart label ∅ (H i)) ih
    | true =>
      simpa [mixedMatrixCommutator, localPart, stepParity, paritySupport,
        singleton_symmDiff_toggle] using
        hasGrade_commutator label {i} (paritySupport (w.map stepParity))
          (hasGrade_gradePart label {i} (H i)) ih

/-- The concrete distance mask retains a word exactly at its actual grade size. -/
theorem distancePart_mixed_localParts (label : X → ι → Bool)
    (H : ι → Matrix X X R) (w : List (ι × Bool))
    {P : Matrix X X R} (hP : HasGrade label ∅ P) (k : ℕ) :
    distancePart label k (mixedMatrixCommutator (localPart label H) w P) =
      if (paritySupport (w.map stepParity)).card = k
      then mixedMatrixCommutator (localPart label H) w P else 0 :=
  distancePart_of_hasGrade label _ (hasGrade_mixed_localParts label H w hP) k

/-- Reaching the length of an expanded operator word forces all distinct odd steps. -/
theorem maximal_steps_iff (w : List (ι × Bool)) :
    (paritySupport (w.map stepParity)).card = w.length ↔
      ∃ l : List ι, l.Nodup ∧ w = l.map (fun i => (i, true)) := by
  have lift : ∀ (w : List (ι × Bool)) (l : List ι),
      w.map stepParity = l.map some → w = l.map (fun i => (i, true)) := by
    intro w
    induction w with
    | nil =>
      intro l h
      cases l <;> simp_all
    | cons step w ih =>
      intro l h
      obtain ⟨i, b⟩ := step
      cases l with
      | nil => simp at h
      | cons j l =>
        cases b with
        | false => simp [stepParity] at h
        | true =>
          simp only [List.map_cons, stepParity, if_true, Option.some.injEq,
            List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          simp [ih l h]
  constructor
  · intro h
    have h' : (paritySupport (w.map stepParity)).card = (w.map stepParity).length := by
      simpa using h
    obtain ⟨l, hl, hw⟩ := (maximal_paritySupport_iff (w.map stepParity)).mp h'
    exact ⟨l, hl, lift w l hw⟩
  · rintro ⟨l, hl, rfl⟩
    have h := (maximal_paritySupport_iff (l.map some)).mpr ⟨l, hl, rfl⟩
    simpa [List.map_map, stepParity, Function.comp_def] using h

/-- Every non-maximal expanded word is killed by the highest-distance mask. -/
theorem highestDistance_word_eq_zero (label : X → ι → Bool)
    (H : ι → Matrix X X R) (w : List (ι × Bool))
    {P : Matrix X X R} (hP : HasGrade label ∅ P)
    (hw : ¬ ∃ l : List ι, l.Nodup ∧ w = l.map (fun i => (i, true))) :
    distancePart label w.length (mixedMatrixCommutator (localPart label H) w P) = 0 := by
  rw [distancePart_mixed_localParts label H w hP]
  exact if_neg (fun h => hw ((maximal_steps_iff w).mp h))

section WordExpansion

variable {α β : Type*}

/-- All words of a prescribed length on a finite list alphabet, with multiplicity. -/
def words (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | k + 1 => alphabet.flatMap (fun i => (words alphabet k).map (List.cons i))

theorem length_of_mem_words (alphabet : List α) (k : ℕ) (w : List α)
    (hw : w ∈ words alphabet k) : w.length = k := by
  induction k generalizing w with
  | zero => simpa [words] using hw
  | succ k ih =>
    simp only [words, List.mem_flatMap] at hw
    obtain ⟨i, _, hw⟩ := hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    simp [ih v hv]

theorem sum_map_flatMap (alphabet : List α) (g : α → List β)
    (f : β → Matrix X X R) :
    ((alphabet.flatMap g).map f).sum =
      (alphabet.map (fun a => ((g a).map f).sum)).sum := by
  induction alphabet with
  | nil => simp
  | cons a alphabet ih => simp [ih]

theorem matrixCommutator_add_left (A B T : Matrix X X R) :
    matrixCommutator (A + B) T = matrixCommutator A T + matrixCommutator B T := by
  unfold matrixCommutator
  noncomm_ring

theorem matrixCommutator_add_right (A T U : Matrix X X R) :
    matrixCommutator A (T + U) = matrixCommutator A T + matrixCommutator A U := by
  unfold matrixCommutator
  noncomm_ring

theorem matrixCommutator_list_sum_left (As : List (Matrix X X R)) (T : Matrix X X R) :
    matrixCommutator As.sum T = (As.map (fun A => matrixCommutator A T)).sum := by
  induction As with
  | nil => simp [matrixCommutator]
  | cons A As ih => simp [matrixCommutator_add_left, ih]

theorem matrixCommutator_list_sum_right (A : Matrix X X R) (Ts : List (Matrix X X R)) :
    matrixCommutator A Ts.sum = (Ts.map (fun T => matrixCommutator A T)).sum := by
  induction Ts with
  | nil => simp [matrixCommutator]
  | cons T Ts ih => simp [matrixCommutator_add_right, ih]

/-- The actual iterated commutator with a sum expands into all operator words.
No commutation or grading hypothesis is used in this algebraic identity. -/
theorem iterate_commutator_word_expansion (alphabet : List α)
    (H : α → Matrix X X R) (P : Matrix X X R) (k : ℕ) :
    (fun T => matrixCommutator (alphabet.map H).sum T)^[k] P =
      ((words alphabet k).map (fun w => mixedMatrixCommutator H w P)).sum := by
  induction k with
  | zero => simp [words, mixedMatrixCommutator]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, matrixCommutator_list_sum_left]
    simp only [words, sum_map_flatMap, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_apply]
    rw [matrixCommutator_list_sum_right]
    simp [List.map_map, mixedMatrixCommutator, Function.comp_def]

end WordExpansion

theorem distancePart_add (label : X → ι → Bool) (k : ℕ) (A B : Matrix X X R) :
    distancePart label k (A + B) = distancePart label k A + distancePart label k B := by
  ext a b
  by_cases h : (gradeOf label a b).card = k <;> simp [distancePart, h]

theorem distancePart_list_sum (label : X → ι → Bool) (k : ℕ)
    (As : List (Matrix X X R)) :
    distancePart label k As.sum = (As.map (distancePart label k)).sum := by
  induction As with
  | nil => ext a b; simp [distancePart]
  | cons A As ih => simp [distancePart_add, ih]

theorem sum_map_ite_filter {α : Type*} (xs : List α) (p : α → Prop) [DecidablePred p]
    (f : α → Matrix X X R) :
    (xs.map (fun x => if p x then f x else 0)).sum =
      ((xs.filter (fun x => decide (p x))).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases h : p x <;> simp [h, ih]

/-- The actual highest-distance part is exactly the sum of the retained step words. -/
theorem highest_distance_word_expansion (label : X → ι → Bool)
    (H : ι → Matrix X X R) (alphabet : List (ι × Bool))
    {P : Matrix X X R} (hP : HasGrade label ∅ P) (k : ℕ) :
    distancePart label k
      ((fun T => matrixCommutator (alphabet.map (localPart label H)).sum T)^[k] P) =
      (((words alphabet k).filter (fun w =>
        decide ((paritySupport (w.map stepParity)).card = k))).map
          (fun w => mixedMatrixCommutator (localPart label H) w P)).sum := by
  rw [iterate_commutator_word_expansion, distancePart_list_sum]
  simp only [List.map_map]
  have hmap : (fun w => distancePart label k
      (mixedMatrixCommutator (localPart label H) w P)) =
      (fun w => if (paritySupport (w.map stepParity)).card = k
        then mixedMatrixCommutator (localPart label H) w P else 0) := by
    funext w
    exact distancePart_mixed_localParts label H w hP k
  simp only [Function.comp_def, hmap]
  exact sum_map_ite_filter _ _ _

/-- Every word retained in the expansion is an order of distinct odd blocks. -/
theorem retained_word_distinct_odd (alphabet : List (ι × Bool)) (k : ℕ)
    (w : List (ι × Bool))
    (hw : w ∈ (words alphabet k).filter (fun v =>
      decide ((paritySupport (v.map stepParity)).card = k))) :
    ∃ l : List ι, l.Nodup ∧ w = l.map (fun i => (i, true)) := by
  obtain ⟨hw, hg⟩ := List.mem_filter.mp hw
  have hlen := length_of_mem_words alphabet k w hw
  apply (maximal_steps_iff w).mp
  simpa [hlen] using hg

/-- Expand each original block index into its even and odd choices. -/
def expandedAlphabet (alphabet : List ι) : List (ι × Bool) :=
  alphabet.flatMap (fun i => [(i, false), (i, true)])

theorem sum_expanded_localParts (label : X → ι → Bool)
    (H : ι → Matrix X X R) (hH : ∀ i, LocalAt label i (H i)) (alphabet : List ι) :
    ((expandedAlphabet alphabet).map (localPart label H)).sum = (alphabet.map H).sum := by
  induction alphabet with
  | nil => simp [expandedAlphabet]
  | cons i alphabet ih =>
    simp only [expandedAlphabet, List.flatMap_cons, List.map_append, List.sum_append]
    change (gradePart label ∅ (H i) + (gradePart label {i} (H i) + 0)) +
      ((expandedAlphabet alphabet).map (localPart label H)).sum =
        H i + (alphabet.map H).sum
    rw [add_zero, ← local_split label i (hH i), ih]

/-- Highest-distance word expansion for the original sum of actual local matrices. -/
theorem highest_distance_local_sum (label : X → ι → Bool)
    (H : ι → Matrix X X R) (hH : ∀ i, LocalAt label i (H i))
    (alphabet : List ι) {P : Matrix X X R} (hP : HasGrade label ∅ P) (k : ℕ) :
    distancePart label k ((fun T => matrixCommutator (alphabet.map H).sum T)^[k] P) =
      (((words (expandedAlphabet alphabet) k).filter (fun w =>
        decide ((paritySupport (w.map stepParity)).card = k))).map
          (fun w => mixedMatrixCommutator (localPart label H) w P)).sum := by
  rw [← sum_expanded_localParts label H hH alphabet]
  exact highest_distance_word_expansion label H (expandedAlphabet alphabet) hP k

/-- The same actual identity with the full finite-index sum used in the manuscript. -/
theorem highest_distance_total_sum (label : X → ι → Bool)
    (H : ι → Matrix X X R) (hH : ∀ i, LocalAt label i (H i))
    {P : Matrix X X R} (hP : HasGrade label ∅ P) (k : ℕ) :
    distancePart label k ((fun T => matrixCommutator (∑ i, H i) T)^[k] P) =
      (((words (expandedAlphabet (Finset.univ : Finset ι).toList) k).filter (fun w =>
        decide ((paritySupport (w.map stepParity)).card = k))).map
          (fun w => mixedMatrixCommutator (localPart label H) w P)).sum := by
  simpa only [Finset.sum_map_toList] using
    highest_distance_local_sum label H hH (Finset.univ : Finset ι).toList hP k

theorem matrix_list_sum_apply (As : List (Matrix X X R)) (a b : X) :
    As.sum a b = (As.map (fun A => A a b)).sum := by
  induction As with
  | nil => rfl
  | cons A As ih => simp [ih]

/-- Actual entrywise Hamming bandwidth of an iterated commutator with a local sum. -/
theorem iterated_local_sum_bandwidth (label : X → ι → Bool)
    (H : ι → Matrix X X R) (hH : ∀ i, LocalAt label i (H i))
    (alphabet : List ι) {P : Matrix X X R} (hP : HasGrade label ∅ P)
    (k : ℕ) (a b : X) (hab : k < (gradeOf label a b).card) :
    ((fun T => matrixCommutator (alphabet.map H).sum T)^[k] P) a b = 0 := by
  rw [← sum_expanded_localParts label H hH alphabet,
    iterate_commutator_word_expansion, matrix_list_sum_apply]
  simp only [List.map_map, Function.comp_def]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  apply hasGrade_mixed_localParts label H w hP a b
  intro heq
  have hbound := card_paritySupport_le (w.map stepParity)
  have hlen := length_of_mem_words (expandedAlphabet alphabet) k w hw
  have hcard := congrArg Finset.card heq
  simp only [List.length_map] at hbound
  omega

/-- The full finite-index bandwidth statement used by common-phase extraction. -/
theorem iterated_total_sum_bandwidth (label : X → ι → Bool)
    (H : ι → Matrix X X R) (hH : ∀ i, LocalAt label i (H i))
    {P : Matrix X X R} (hP : HasGrade label ∅ P)
    (k : ℕ) (a b : X) (hab : k < (gradeOf label a b).card) :
    ((fun T => matrixCommutator (∑ i, H i) T)^[k] P) a b = 0 := by
  simpa only [Finset.sum_map_toList] using
    iterated_local_sum_bandwidth label H hH (Finset.univ : Finset ι).toList hP k a b hab

/-- A retained all-odd word evaluates to the original crossing masks alone. -/
theorem mixed_localParts_allOdd (label : X → ι → Bool)
    (H : ι → Matrix X X R) (l : List ι) (P : Matrix X X R) :
    mixedMatrixCommutator (localPart label H) (l.map (fun i => (i, true))) P =
      mixedMatrixCommutator (fun i => gradePart label {i} (H i)) l P := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change matrixCommutator (gradePart label {i} (H i))
        (mixedMatrixCommutator (localPart label H) (l.map (fun i => (i, true))) P) =
      matrixCommutator (gradePart label {i} (H i))
        (mixedMatrixCommutator (fun i => gradePart label {i} (H i)) l P)
    rw [ih]

/-- The true-fiber crossing mask in one logical coordinate. -/
def crossingPart (label : X → ι → Bool) (i : ι) (A : Matrix X X R) :
    Matrix X X R := fun a b => if label a i ≠ label b i then A a b else 0

/-- For an actual local matrix, its single-coordinate grade is its true-fiber strip. -/
theorem crossingPart_eq_gradePart (label : X → ι → Bool) (i : ι)
    {A : Matrix X X R} (hA : LocalAt label i A) :
    crossingPart label i A = gradePart label {i} A := by
  ext a b
  by_cases hbit : label a i ≠ label b i
  · have hzero : gradeOf label a b ≠ ∅ := by
      intro h
      have hm := (mem_gradeOf label a b i).mpr hbit
      simp [h] at hm
    by_cases hg : gradeOf label a b = {i}
    · simp [crossingPart, gradePart, hbit, hg]
    · simp [crossingPart, gradePart, hbit, hg, hA a b hzero hg]
  · have hg : gradeOf label a b ≠ {i} := by
      intro h
      have hm : i ∈ gradeOf label a b := by simp [h]
      exact hbit ((mem_gradeOf label a b i).mp hm)
    simp [crossingPart, gradePart, hbit, hg]

/-- The diagonal sign involution defining the true fibers. -/
def fiberSign (label : X → ι → Bool) (i : ι) : Matrix X X R :=
  Matrix.diagonal (fun a => if label a i then -1 else 1)

/-- Entrywise verification of twice the true-fiber strip, over any ring. -/
theorem twice_crossingPart (label : X → ι → Bool) (i : ι) (A : Matrix X X R) :
    (2 : ℕ) • crossingPart label i A = A - fiberSign label i * A * fiberSign label i := by
  ext a b
  simp only [two_nsmul, Matrix.add_apply, Matrix.sub_apply, fiberSign,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases h₁ : label a i <;> cases h₂ : label b i <;> simp [crossingPart, h₁, h₂]

section ConcreteLocalLift

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- A concrete tensor-coordinate lift: the inner matrix in coordinate `i`,
and identity matrices on every other coordinate. -/
def localLift (K : Matrix Y Y R) (i : ι) : Matrix (ι → Y) (ι → Y) R :=
  fun a b => if ∀ j, j ≠ i → a j = b j then K (a i) (b i) else 0

/-- Concrete tensor-coordinate lifts satisfy the locality needed above. -/
theorem localAt_localLift (g : Y → Bool) (K : Matrix Y Y R) (i : ι) :
    LocalAt (fun a j => g (a j)) i (localLift K i) := by
  intro a b hzero hone
  by_cases hraw : ∀ j, j ≠ i → a j = b j
  · have hs : gradeOf (fun a j => g (a j)) a b ⊆ {i} := by
      intro j hj
      apply Finset.mem_singleton.mpr
      by_contra hji
      exact ((mem_gradeOf (fun a j => g (a j)) a b j).mp hj)
        (congrArg g (hraw j hji))
    exact False.elim ((Finset.subset_singleton_iff.mp hs).elim hzero hone)
  · simp [localLift, hraw]

/-- Concrete highest-distance expansion on a full product point space.
Neither locality nor the grading propagation law is an assumption here. -/
theorem highest_distance_lifted_sum (g : Y → Bool) (K : ι → Matrix Y Y R)
    (p : (ι → Y) → R) (k : ℕ) :
    distancePart (fun a j => g (a j)) k
      ((fun T => matrixCommutator (∑ i, localLift (K i) i) T)^[k] (Matrix.diagonal p)) =
      (((words (expandedAlphabet (Finset.univ : Finset ι).toList) k).filter (fun w =>
        decide ((paritySupport (w.map stepParity)).card = k))).map
          (fun w => mixedMatrixCommutator
            (localPart (fun a j => g (a j)) (fun i => localLift (K i) i))
            w (Matrix.diagonal p))).sum := by
  exact highest_distance_total_sum (fun a j => g (a j))
    (fun i => localLift (K i) i) (fun i => localAt_localLift g (K i) i)
    (hasGrade_diagonal (fun a j => g (a j)) p) k

/-- Bandwidth on a full product space for concrete local lifts and a point multiplier. -/
theorem iterated_lifted_sum_bandwidth (g : Y → Bool) (K : ι → Matrix Y Y R)
    (p : (ι → Y) → R) (k : ℕ) (a b : ι → Y)
    (hab : k < (gradeOf (fun a j => g (a j)) a b).card) :
    ((fun T => matrixCommutator (∑ i, localLift (K i) i) T)^[k]
      (Matrix.diagonal p)) a b = 0 := by
  exact iterated_total_sum_bandwidth (fun a j => g (a j))
    (fun i => localLift (K i) i) (fun i => localAt_localLift g (K i) i)
    (hasGrade_diagonal (fun a j => g (a j)) p) k a b hab

end ConcreteLocalLift

section Regrouping

theorem mem_words_iff {α : Type*} (alphabet : List α) (k : ℕ) (w : List α) :
    w ∈ words alphabet k ↔ w.length = k ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction k generalizing w with
  | zero => cases w <;> simp [words]
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons a w =>
      constructor
      · intro hw
        obtain ⟨b, hb, hw⟩ := List.mem_flatMap.mp hw
        obtain ⟨v, hv, heq⟩ := List.mem_map.mp hw
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        obtain ⟨hlen, hm⟩ := (ih v).mp hv
        exact ⟨by simp [hlen], by simpa using And.intro hb hm⟩
      · rintro ⟨hlen, hm⟩
        apply List.mem_flatMap.mpr
        refine ⟨a, hm a (by simp), List.mem_map.mpr ?_⟩
        refine ⟨w, (ih w).mpr ?_, rfl⟩
        exact ⟨by simpa using hlen, fun b hb => hm b (by simp [hb])⟩

theorem nodup_words {α : Type*} (alphabet : List α) (ha : alphabet.Nodup) (k : ℕ) :
    (words alphabet k).Nodup := by
  induction k with
  | zero => simp [words]
  | succ k ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a _
      exact ih.map (fun _ _ h => (List.cons.inj h).2)
    · exact ha.imp (fun {a b} hab z hza hzb => by
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hza
        obtain ⟨v, _, h⟩ := List.mem_map.mp hzb
        exact hab (List.cons.inj h).1.symm)

theorem nodup_expandedAlphabet (alphabet : List ι) (ha : alphabet.Nodup) :
    (expandedAlphabet alphabet).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i _
    simp
  · exact ha.imp (fun {a b} hab z hza hzb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hza hzb
      rcases hza with rfl | rfl <;> rcases hzb with h | h <;>
        exact hab (Prod.mk.inj h).1)

theorem mem_expanded_univ (step : ι × Bool) :
    step ∈ expandedAlphabet (Finset.univ : Finset ι).toList := by
  obtain ⟨i, b⟩ := step
  apply List.mem_flatMap.mpr
  refine ⟨i, by simp, ?_⟩
  cases b <;> simp

theorem maximal_steps_ordering_iff (w : List (ι × Bool)) (s : Finset ι) :
    paritySupport (w.map stepParity) = s ∧ w.length = s.card ↔
      ∃ l ∈ orderings s, w = l.map (fun i => (i, true)) := by
  constructor
  · rintro ⟨hs, hlen⟩
    have hmax : (paritySupport (w.map stepParity)).card = w.length := by rw [hs, hlen]
    obtain ⟨l, hl, rfl⟩ := (maximal_steps_iff w).mp hmax
    have hs' : l.toFinset = s := by
      simpa [List.map_map, stepParity, Function.comp_def,
        paritySupport_map_some_of_nodup l hl] using hs
    refine ⟨l, (mem_orderings_iff s l).mpr ?_, rfl⟩
    apply (List.perm_ext_iff_of_nodup hl (Finset.nodup_toList s)).mpr
    intro a
    simp [← hs']
  · rintro ⟨l, hl, rfl⟩
    have hp := (mem_orderings_iff s l).mp hl
    have hn := hp.nodup_iff.mpr (Finset.nodup_toList s)
    constructor
    · simp only [List.map_map, stepParity, Function.comp_def, if_true]
      rw [paritySupport_map_some_of_nodup l hn]
      ext a
      simpa using hp.mem_iff
    · simpa using hp.length_eq

/-- The explicit retained list; it has no duplicate words for the full alphabet. -/
noncomputable def retainedWords (k : ℕ) : List (List (ι × Bool)) :=
  (words (expandedAlphabet (Finset.univ : Finset ι).toList) k).filter
    (fun w => decide ((paritySupport (w.map stepParity)).card = k))

theorem nodup_retainedWords (k : ℕ) : (retainedWords (ι := ι) k).Nodup :=
  (nodup_words _ (nodup_expandedAlphabet _ (Finset.nodup_toList _)) k).filter _

theorem mem_retainedWords_iff (k : ℕ) (w : List (ι × Bool)) :
    w ∈ retainedWords k ↔
      w.length = k ∧ (paritySupport (w.map stepParity)).card = k := by
  simp [retainedWords, List.mem_filter, mem_words_iff, mem_expanded_univ]

/-- A fiber of retained words is exactly the image of all orders of that support. -/
theorem retainedWords_fiber (k : ℕ) (s : Finset ι) (hs : s.card = k) :
    (retainedWords (ι := ι) k).toFinset.filter
        (fun w => paritySupport (w.map stepParity) = s) =
      (orderings s).image (List.map (fun i => (i, true))) := by
  ext w
  simp only [Finset.mem_filter, List.mem_toFinset, mem_retainedWords_iff,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hlen, _⟩, hgrade⟩
    obtain ⟨l, hl, hw⟩ := (maximal_steps_ordering_iff w s).mp ⟨hgrade, hlen.trans hs.symm⟩
    exact ⟨l, hl, hw.symm⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hgrade, hlen⟩ := (maximal_steps_ordering_iff _ s).mpr ⟨l, hl, rfl⟩
    exact ⟨⟨hlen.trans hs, by rw [hgrade, hs]⟩, hgrade⟩

/-- Regroup the actual retained operator words by their distinct-block support. -/
theorem regroup_retained_words (label : X → ι → Bool)
    (H : ι → Matrix X X R) (P : Matrix X X R) (k : ℕ) :
    (∑ w ∈ (retainedWords (ι := ι) k).toFinset,
      mixedMatrixCommutator (localPart label H) w P) =
    ∑ s ∈ (Finset.univ : Finset ι).powersetCard k, ∑ l ∈ orderings s,
      mixedMatrixCommutator (fun i => gradePart label {i} (H i)) l P := by
  have hmap : ∀ w ∈ (retainedWords (ι := ι) k).toFinset,
      paritySupport (w.map stepParity) ∈ (Finset.univ : Finset ι).powersetCard k := by
    intro w hw
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, ((mem_retainedWords_iff k w).mp
      (List.mem_toFinset.mp hw)).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro s hs
  rw [retainedWords_fiber k s (Finset.mem_powersetCard.mp hs).2, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro l _
    exact mixed_localParts_allOdd label H l P
  · intro l₁ _ l₂ _ h
    exact List.map_injective_iff.mpr (fun _ _ heq => (Prod.mk.inj heq).1) h

/-- The exact highest-distance factorial identity, derived from concrete matrix grading.
The only commutation assumption concerns the actual distinct crossing matrices. -/
theorem highest_distance_factorial_identity (label : X → ι → Bool)
    (H : ι → Matrix X X R) (hH : ∀ i, LocalAt label i (H i))
    (hcomm : ∀ i j, i ≠ j →
      gradePart label {i} (H i) * gradePart label {j} (H j) =
      gradePart label {j} (H j) * gradePart label {i} (H i))
    {P : Matrix X X R} (hP : HasGrade label ∅ P) (k : ℕ) :
    distancePart label k ((fun T => matrixCommutator (∑ i, H i) T)^[k] P) =
      k.factorial • (∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
        mixedMatrixCommutator (fun i => gradePart label {i} (H i)) s.toList P) := by
  rw [highest_distance_total_sum label H hH hP]
  change ((retainedWords k).map (fun w => mixedMatrixCommutator (localPart label H) w P)).sum = _
  rw [← List.sum_toFinset _ (nodup_retainedWords k), regroup_retained_words,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard := (Finset.mem_powersetCard.mp hs).2
  have hfun (i : ι) : ProtectedCrossings.commutator (gradePart label {i} (H i)) =
      matrixCommutator (gradePart label {i} (H i)) := rfl
  simpa only [hcard, applyWord, mixedMatrixCommutator, hfun] using
    sum_orderings_commutator (fun i => gradePart label {i} (H i)) hcomm s P

end Regrouping

end ApproxDegree.OperatorGrading
end

-- LocalCommutation.lean
section
/-!
# Commutation of concrete tensor-coordinate lifts

The entries of `OperatorGrading.localLift` imply that matrices lifted to
distinct coordinates commute over a commutative coefficient ring. This is
proved by evaluating the matrix product at its unique possible intermediate
point, rather than by assuming tensor locality or matrix commutation.

Actual Boolean crossing masks are again local lifts, so the result discharges
the commutation hypothesis of the highest-distance factorial identity.
-/

namespace ApproxDegree.LocalCommutation

open scoped BigOperators
open OperatorGrading

variable {ι Y R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Y] [DecidableEq Y] [CommRing R]

/-- A product of lifts on two distinct coordinates has exactly one possible
nonzero intermediate point in the defining matrix sum. -/
theorem localLift_mul_apply (K L : Matrix Y Y R) {i j : ι} (hij : i ≠ j)
    (a b : ι → Y) :
    (localLift K i * localLift L j) a b =
      if ∀ l, l ≠ i → l ≠ j → a l = b l
      then K (a i) (b i) * L (a j) (b j) else 0 := by
  let c : ι → Y := Function.update a i (b i)
  have hac : ∀ l, l ≠ i → a l = c l := by
    intro l hli
    simp [c, hli]
  have hcb : (∀ l, l ≠ j → c l = b l) ↔
      (∀ l, l ≠ i → l ≠ j → a l = b l) := by
    constructor
    · intro h l hli hlj
      simpa [c, hli] using h l hlj
    · intro h l hlj
      by_cases hli : l = i
      · subst l
        simp [c]
      · simpa [c, hli] using h l hli hlj
  have hsum : (localLift K i * localLift L j) a b =
      localLift K i a c * localLift L j c b := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single c
    · intro d _ hdc
      by_cases had : ∀ l, l ≠ i → a l = d l
      · by_cases hdb : ∀ l, l ≠ j → d l = b l
        · exfalso
          apply hdc
          funext l
          by_cases hli : l = i
          · subst l
            simpa [c] using hdb i hij
          · simpa [c, hli] using (had l hli).symm
        · simp [localLift, hdb]
      · simp [localLift, had]
    · intro hc
      exact False.elim (hc (Finset.mem_univ c))
  rw [hsum]
  by_cases hs : ∀ l, l ≠ i → l ≠ j → a l = b l
  · have hcb' := hcb.mpr hs
    simp only [localLift, if_pos hac, if_pos hcb', if_pos hs]
    simp [c, Ne.symm hij]
  · have hcb' : ¬ ∀ l, l ≠ j → c l = b l := fun h => hs (hcb.mp h)
    simp [localLift, hcb', hs]

/-- Matrices acting in distinct tensor coordinates commute. Only the scalar
coefficient ring is assumed commutative. -/
theorem localLift_commute (K L : Matrix Y Y R) {i j : ι} (hij : i ≠ j) :
    localLift K i * localLift L j = localLift L j * localLift K i := by
  ext a b
  rw [localLift_mul_apply K L hij, localLift_mul_apply L K (Ne.symm hij)]
  have hs : (∀ l, l ≠ i → l ≠ j → a l = b l) ↔
      (∀ l, l ≠ j → l ≠ i → a l = b l) := by
    constructor <;> intro h l h₁ h₂ <;> exact h l h₂ h₁
  by_cases hleft : ∀ l, l ≠ i → l ≠ j → a l = b l
  · have hright := hs.mp hleft
    simp only [if_pos hleft, if_pos hright, mul_comm]
  · have hright : ¬ ∀ l, l ≠ j → l ≠ i → a l = b l := fun h => hleft (hs.mpr h)
    simp only [if_neg hleft, if_neg hright]

/-- The actual one-block matrix retaining entries between opposite fibers. -/
def innerCrossing (g : Y → Bool) (K : Matrix Y Y R) : Matrix Y Y R :=
  fun a b => if g a ≠ g b then K a b else 0

omit [Fintype Y] in
/-- Taking a true-fiber crossing mask commutes with concrete coordinate lifting. -/
theorem crossingPart_localLift (g : Y → Bool) (K : Matrix Y Y R) (i : ι) :
    crossingPart (fun a j => g (a j)) i (localLift K i) =
      localLift (innerCrossing g K) i := by
  ext a b
  by_cases hlocal : ∀ j, j ≠ i → a j = b j <;>
    by_cases hbit : g (a i) ≠ g (b i) <;>
    simp [crossingPart, localLift, innerCrossing, hlocal, hbit]

/-- The singleton logical-grade mask of a local lift is the lift of the
one-block crossing matrix. -/
theorem gradePart_localLift (g : Y → Bool) (K : Matrix Y Y R) (i : ι) :
    gradePart (fun a j => g (a j)) {i} (localLift K i) =
      localLift (innerCrossing g K) i := by
  calc
    _ = crossingPart (fun a j => g (a j)) i (localLift K i) :=
      (crossingPart_eq_gradePart _ i (localAt_localLift g K i)).symm
    _ = _ := crossingPart_localLift g K i

/-- Distinct actual crossing masks commute, without an operator commutation
hypothesis. -/
theorem crossingPart_localLift_commute (g : Y → Bool) (K L : Matrix Y Y R)
    {i j : ι} (hij : i ≠ j) :
    crossingPart (fun a l => g (a l)) i (localLift K i) *
        crossingPart (fun a l => g (a l)) j (localLift L j) =
      crossingPart (fun a l => g (a l)) j (localLift L j) *
        crossingPart (fun a l => g (a l)) i (localLift K i) := by
  simp only [crossingPart_localLift]
  exact localLift_commute _ _ hij

/-- The precise singleton-mask commutation input expected by OperatorGrading. -/
theorem gradePart_localLift_commute (g : Y → Bool) (K L : Matrix Y Y R)
    {i j : ι} (hij : i ≠ j) :
    gradePart (fun a l => g (a l)) {i} (localLift K i) *
        gradePart (fun a l => g (a l)) {j} (localLift L j) =
      gradePart (fun a l => g (a l)) {j} (localLift L j) *
        gradePart (fun a l => g (a l)) {i} (localLift K i) := by
  simp only [gradePart_localLift]
  exact localLift_commute _ _ hij

set_option maxHeartbeats 800000 in
/-- The protected factorial identity for physical coordinate lifts and an
arbitrary point multiplier. Locality, grading propagation, and distinct
crossing commutation are all discharged by concrete matrix proofs. -/
theorem highest_distance_localLift_factorial_identity (g : Y → Bool)
    (K : ι → Matrix Y Y R) (p : (ι → Y) → R) (k : ℕ) :
    distancePart (fun a j => g (a j)) k
        ((fun T => matrixCommutator (∑ i, localLift (K i) i) T)^[k]
          (Matrix.diagonal p)) =
      k.factorial • (∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
        mixedMatrixCommutator (fun i => localLift (innerCrossing g (K i)) i)
          s.toList (Matrix.diagonal p)) := by
  simpa only [gradePart_localLift] using
    highest_distance_factorial_identity (fun a j => g (a j))
      (fun i => localLift (K i) i) (fun i => localAt_localLift g (K i) i)
      (fun i j hij => gradePart_localLift_commute (ι := ι) (Y := Y) (R := R)
        g (K i) (K j) (i := i) (j := j) hij)
      (hasGrade_diagonal (fun a j => g (a j)) p) k

end ApproxDegree.LocalCommutation
end

-- HilbertPointBridge.lean
section
/-!
# Actual Euclidean Hilbert coordinates for a true-fiber exchange pair

All vector norms in this module are the `EuclideanSpace` Hilbert norm.
The representing matrix is defined using `Matrix.toEuclideanLin.symm`,
and its coordinate action and Hermiticity are proved rather than assumed.
-/

open scoped BigOperators ComplexConjugate

namespace ApproxDegree.HilbertPointBridge

noncomputable section

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

abbrev PointHilbert (Y : Type*) := EuclideanSpace ℂ Y

/-- The actual coordinate matrix of a linear operator on Euclidean space. -/
def operatorMatrix (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y) : Matrix Y Y ℂ :=
  Matrix.toEuclideanLin.symm L

/-- Its matrix-vector sums equal the coordinates of the original operator. -/
theorem operatorMatrix_apply (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y)
    (v : PointHilbert Y) (x : Y) :
    ∑ y, operatorMatrix L x y * v y = (L v) x := by
  have h : Matrix.toEuclideanLin (operatorMatrix L) = L :=
    LinearEquiv.apply_symm_apply Matrix.toEuclideanLin L
  exact congrArg (fun T : PointHilbert Y →ₗ[ℂ] PointHilbert Y => (T v) x) h

/-- A symmetric Hilbert operator has a Hermitian coordinate matrix. -/
theorem operatorMatrix_isHermitian (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y)
    (hL : L.IsSymmetric) : (operatorMatrix L).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  simpa only [operatorMatrix, LinearEquiv.apply_symm_apply] using hL

theorem operatorMatrix_mul (L M : PointHilbert Y →ₗ[ℂ] PointHilbert Y) :
    operatorMatrix (L * M) = operatorMatrix L * operatorMatrix M := by
  exact Matrix.toLpLin_symm_comp 2 2 2 L M

theorem operatorMatrix_sub (L M : PointHilbert Y →ₗ[ℂ] PointHilbert Y) :
    operatorMatrix (L - M) = operatorMatrix L - operatorMatrix M :=
  map_sub Matrix.toEuclideanLin.symm L M

theorem operatorMatrix_smul_real (c : ℝ) (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y) :
    operatorMatrix (c • L) = c • operatorMatrix L :=
  LinearMap.map_smul_of_tower Matrix.toEuclideanLin.symm.toLinearMap c L

def signValue (b : Bool) : ℂ := if b then -1 else 1

/-- The actual pointwise Boolean sign operator, with the Euclidean Hilbert norm. -/
def signOperator (g : Y → Bool) : PointHilbert Y →L[ℂ] PointHilbert Y :=
  (Matrix.toEuclideanLin (Matrix.diagonal (fun y => signValue (g y)))).toContinuousLinearMap

theorem signOperator_apply (g : Y → Bool) (v : PointHilbert Y) (y : Y) :
    signOperator g v y = signValue (g y) * v y := by
  change Matrix.mulVec (Matrix.diagonal (fun y => signValue (g y))) (fun y => v y) y = _
  exact Matrix.mulVec_diagonal _ _ y

/-- The pointwise sign operator is self-adjoint in the actual Hilbert space. -/
theorem signOperator_isSelfAdjoint (g : Y → Bool) : IsSelfAdjoint (signOperator g) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  change (Matrix.toEuclideanLin (Matrix.diagonal (fun y => signValue (g y)))).IsSymmetric
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro y
  cases g y <;> simp [signValue, IsSelfAdjoint]

/-- The square of the sign operator is the identity. -/
theorem signOperator_involution (g : Y → Bool) (v : PointHilbert Y) :
    signOperator g (signOperator g v) = v := by
  ext y
  rw [signOperator_apply, signOperator_apply]
  cases g y <;> simp [signValue]

theorem operatorMatrix_signOperator (g : Y → Bool) :
    operatorMatrix (signOperator g : PointHilbert Y →ₗ[ℂ] PointHilbert Y) =
      Matrix.diagonal (fun y => signValue (g y)) := by
  exact LinearEquiv.symm_apply_apply Matrix.toEuclideanLin _

/-- The literal real-half conjugation strip has exactly the actual
opposite-fiber matrix entries, including when the original operator is not Hermitian. -/
theorem operatorMatrix_crossing_expanded (g : Y → Bool)
    (H : PointHilbert Y →L[ℂ] PointHilbert Y) :
    operatorMatrix (((1 / 2 : ℝ) • (H - signOperator g * H * signOperator g)) :
      PointHilbert Y →ₗ[ℂ] PointHilbert Y) =
      LocalCommutation.innerCrossing g
        (operatorMatrix (H : PointHilbert Y →ₗ[ℂ] PointHilbert Y)) := by
  rw [operatorMatrix_smul_real, operatorMatrix_sub, operatorMatrix_mul,
    operatorMatrix_mul, operatorMatrix_signOperator]
  ext a b
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change ((1 / 2 : ℝ) : ℂ) *
    (operatorMatrix H.toLinearMap a b -
      signValue (g a) * operatorMatrix H.toLinearMap a b * signValue (g b)) = _
  cases ha : g a <;> cases hb : g b <;>
    simp [LocalCommutation.innerCrossing, signValue, ha, hb] <;> ring

/-- The exact crossing-strip definition used by the filtration construction
has the exact crossing-matrix definition used by coordinate extraction. -/
theorem operatorMatrix_crossingStrip (g : Y → Bool)
    (H : PointHilbert Y →L[ℂ] PointHilbert Y) :
    operatorMatrix (FiltrationOperator.crossingStrip H (signOperator g) :
      PointHilbert Y →ₗ[ℂ] PointHilbert Y) =
      LocalCommutation.innerCrossing g
        (operatorMatrix (H : PointHilbert Y →ₗ[ℂ] PointHilbert Y)) :=
  operatorMatrix_crossing_expanded g H

theorem innerCrossing_operatorMatrix_isHermitian (g : Y → Bool)
    (H : PointHilbert Y →L[ℂ] PointHilbert Y) (hH : IsSelfAdjoint H) :
    (LocalCommutation.innerCrossing g
      (operatorMatrix (H : PointHilbert Y →ₗ[ℂ] PointHilbert Y))).IsHermitian := by
  rw [← operatorMatrix_crossingStrip]
  exact operatorMatrix_isHermitian _
    (FiltrationOperator.crossingStrip_isSelfAdjoint H (signOperator g)
      hH (signOperator_isSelfAdjoint g)).isSymmetric

/-- Turn the two Hilbert vectors into their actual point coordinates. -/
def pointPair (u₀ u₁ : PointHilbert Y) (b : Bool) (y : Y) : ℂ :=
  if b then u₁ y else u₀ y

omit [DecidableEq Y] in
/-- A unit Euclidean vector has sum of squared coordinate norms exactly one. -/
theorem pointPair_normalized (u₀ u₁ : PointHilbert Y)
    (hn₀ : ‖u₀‖ = 1) (hn₁ : ‖u₁‖ = 1) (b : Bool) :
    ∑ y, ‖pointPair u₀ u₁ b y‖ ^ 2 = 1 := by
  cases b
  · change (∑ y, ‖u₀ y‖ ^ 2) = 1
    rw [← EuclideanSpace.norm_sq_eq, hn₀, one_pow]
  · change (∑ y, ‖u₁ y‖ ^ 2) = 1
    rw [← EuclideanSpace.norm_sq_eq, hn₁, one_pow]

/-- Membership in the two sign eigenspaces gives exact support on the true
point fibers. This is a coordinate consequence, not a support hypothesis. -/
theorem pointPair_support (g : Y → Bool) (u₀ u₁ : PointHilbert Y)
    (hf₀ : signOperator g u₀ = u₀) (hf₁ : signOperator g u₁ = -u₁)
    (b : Bool) (y : Y) (h : pointPair u₀ u₁ b y ≠ 0) : g y = b := by
  cases b
  · cases hg : g y
    · rfl
    · exfalso
      apply h
      change u₀ y = 0
      have hc := congrArg (fun v : PointHilbert Y => v y) hf₀
      rw [signOperator_apply] at hc
      have hn : u₀ y = -u₀ y := by simpa [hg, signValue] using hc.symm
      exact CharZero.eq_neg_self_iff.mp hn
  · cases hg : g y
    · exfalso
      apply h
      change u₁ y = 0
      have hc := congrArg (fun v : PointHilbert Y => v y) hf₁
      rw [signOperator_apply] at hc
      have hn : u₁ y = -u₁ y := by simpa [hg, signValue] using hc
      exact CharZero.eq_neg_self_iff.mp hn
    · rfl

/-- Hilbert-space exchange becomes the literal coordinate-sum equations
required by `FiberIntertwining`, with no matrix representation assumption. -/
theorem pointPair_exchange (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y)
    (u₀ u₁ : PointHilbert Y) (κ : ℂ)
    (he₀ : L u₀ = κ • u₁) (he₁ : L u₁ = κ • u₀) (b : Bool) (x : Y) :
    ∑ y, operatorMatrix L x y * pointPair u₀ u₁ b y =
      κ * pointPair u₀ u₁ (!b) x := by
  cases b
  · change (∑ y, operatorMatrix L x y * u₀ y) = κ * u₁ x
    rw [operatorMatrix_apply]
    exact congrArg (fun v : PointHilbert Y => v x) he₀
  · change (∑ y, operatorMatrix L x y * u₁ y) = κ * u₀ x
    rw [operatorMatrix_apply]
    exact congrArg (fun v : PointHilbert Y => v x) he₁

/-- Assemble the three actual point-coordinate construction inputs from a
unit Hilbert exchange pair in the two true sign eigenspaces. -/
theorem pointPair_channel_inputs (g : Y → Bool)
    (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y) (u₀ u₁ : PointHilbert Y) (κ : ℂ)
    (hn₀ : ‖u₀‖ = 1) (hn₁ : ‖u₁‖ = 1)
    (hf₀ : signOperator g u₀ = u₀) (hf₁ : signOperator g u₁ = -u₁)
    (he₀ : L u₀ = κ • u₁) (he₁ : L u₁ = κ • u₀) :
    (∀ b, ∑ y, ‖pointPair u₀ u₁ b y‖ ^ 2 = 1) ∧
    (∀ b y, pointPair u₀ u₁ b y ≠ 0 → g y = b) ∧
    (∀ b x, ∑ y, operatorMatrix L x y * pointPair u₀ u₁ b y =
      κ * pointPair u₀ u₁ (!b) x) :=
  ⟨pointPair_normalized u₀ u₁ hn₀ hn₁,
    pointPair_support g u₀ u₁ hf₀ hf₁, pointPair_exchange L u₀ u₁ κ he₀ he₁⟩

/-- Finite-dimensional spectral theory now yields actual normalized,
true-fiber point vectors exchanged at the genuine Hilbert operator norm.
No eigenvectors, support, normalization, or coordinate exchange sums are inputs. -/
theorem exists_point_exchange_at_opNorm (g : Y → Bool)
    (L : PointHilbert Y →L[ℂ] PointHilbert Y)
    (hL : IsSelfAdjoint L) (hLne : L ≠ 0)
    (hanti : ∀ v, L (signOperator g v) = -signOperator g (L v)) :
    ∃ u : Bool → Y → ℂ,
      (∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) ∧
      (∀ b y, u b y ≠ 0 → g y = b) ∧
      (∀ b x, ∑ y, operatorMatrix (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y) x y * u b y =
        (‖L‖ : ℂ) * u (!b) x) := by
  obtain ⟨u₀, u₁, hn₀, hn₁, hf₀, hf₁, he₀, he₁⟩ :=
    SpectralExchange.exists_true_fiber_exchange_pair L (signOperator g)
      hL hLne (signOperator_isSelfAdjoint g) (signOperator_involution g) hanti
  exact ⟨pointPair u₀ u₁, pointPair_channel_inputs g
    (L : PointHilbert Y →ₗ[ℂ] PointHilbert Y) u₀ u₁ (‖L‖ : ℂ)
    hn₀ hn₁ hf₀ hf₁ he₀ he₁⟩

/-- A nonzero strip of any self-adjoint Euclidean operator yields the actual
normalized fiber vectors and literal inner-crossing coordinate exchange sums.
The sign involution, strip anticommutation, and spectral pair are all derived. -/
theorem exists_point_exchange_for_crossingStrip (g : Y → Bool)
    (H : PointHilbert Y →L[ℂ] PointHilbert Y) (hH : IsSelfAdjoint H)
    (hne : FiltrationOperator.crossingStrip H (signOperator g) ≠ 0) :
    ∃ u : Bool → Y → ℂ,
      (∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) ∧
      (∀ b y, u b y ≠ 0 → g y = b) ∧
      (∀ b x, ∑ y, LocalCommutation.innerCrossing g
          (operatorMatrix (H : PointHilbert Y →ₗ[ℂ] PointHilbert Y)) x y * u b y =
        (‖FiltrationOperator.crossingStrip H (signOperator g)‖ : ℂ) * u (!b) x) := by
  obtain ⟨u, hn, hf, he⟩ := exists_point_exchange_at_opNorm g
    (FiltrationOperator.crossingStrip H (signOperator g))
    (FiltrationOperator.crossingStrip_isSelfAdjoint H (signOperator g)
      hH (signOperator_isSelfAdjoint g)) hne
    (FiltrationOperator.crossingStrip_anticommutes H (signOperator g)
      (signOperator_involution g))
  refine ⟨u, hn, hf, ?_⟩
  simpa only [operatorMatrix_crossingStrip] using he

/-- A finite matrix acting on the actual Euclidean Hilbert space, equipped
with its continuous-operator norm rather than the default matrix norm. -/
def matrixOperator (K : Matrix Y Y ℂ) : PointHilbert Y →L[ℂ] PointHilbert Y :=
  K.toEuclideanLin.toContinuousLinearMap

theorem operatorMatrix_matrixOperator (K : Matrix Y Y ℂ) :
    operatorMatrix (matrixOperator K : PointHilbert Y →ₗ[ℂ] PointHilbert Y) = K :=
  LinearEquiv.symm_apply_apply Matrix.toEuclideanLin K

theorem matrixOperator_isSelfAdjoint (K : Matrix Y Y ℂ) (hK : K.IsHermitian) :
    IsSelfAdjoint (matrixOperator K) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hK

/-- Literal matrix-input version of the norm-scale point-vector construction. -/
theorem exists_point_exchange_for_innerCrossing (g : Y → Bool) (K : Matrix Y Y ℂ)
    (hK : K.IsHermitian)
    (hne : FiltrationOperator.crossingStrip (matrixOperator K) (signOperator g) ≠ 0) :
    ∃ u : Bool → Y → ℂ,
      (∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) ∧
      (∀ b y, u b y ≠ 0 → g y = b) ∧
      (∀ b x, ∑ y, LocalCommutation.innerCrossing g K x y * u b y =
        (‖FiltrationOperator.crossingStrip (matrixOperator K) (signOperator g)‖ : ℂ) *
          u (!b) x) := by
  simpa only [operatorMatrix_matrixOperator] using
    exists_point_exchange_for_crossingStrip g (matrixOperator K)
      (matrixOperator_isSelfAdjoint K hK) hne

end

end ApproxDegree.HilbertPointBridge
end

-- DegreeScaleWitness.lean
section
/-!
# A degree-scale inner witness constructed from polynomial nonapproximation

This connects finite-domain duality, weighted polynomial subspaces, the actual
projection generator, finite-dimensional spectral theory, and exact-fiber point
coordinates. Neither the scale kappa nor an exchange pair is assumed.
-/

open scoped BigOperators

namespace ApproxDegree.DegreeScaleWitness

noncomputable section

variable {X σ : Type*} [Fintype X] [DecidableEq X]

def signTarget (g : X → Bool) (x : X) : ℝ := if g x then -1 else 1

def witnessGenerator (ψ : X → ℝ) (coords : X → σ → ℝ) (d : ℕ) :
    EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ X :=
  FiltrationOperator.generator d fun j => WeightedDualVectors.polynomialSpace ψ coords j.val

def witnessStrip (ψ : X → ℝ) (coords : X → σ → ℝ) (g : X → Bool) (d : ℕ) :
    EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ X :=
  FiltrationOperator.crossingStrip (witnessGenerator ψ coords d)
    (HilbertPointBridge.signOperator g)

def witnessMatrix (ψ : X → ℝ) (coords : X → σ → ℝ) (d : ℕ) : Matrix X X ℂ :=
  HilbertPointBridge.operatorMatrix (witnessGenerator ψ coords d).toLinearMap

omit [DecidableEq X] in
theorem witnessGenerator_isSelfAdjoint (ψ : X → ℝ) (coords : X → σ → ℝ) (d : ℕ) :
    IsSelfAdjoint (witnessGenerator ψ coords d) :=
  FiltrationOperator.generator_isSelfAdjoint d _

theorem witnessMatrix_isHermitian (ψ : X → ℝ) (coords : X → σ → ℝ) (d : ℕ) :
    (witnessMatrix ψ coords d).IsHermitian :=
  HilbertPointBridge.operatorMatrix_isHermitian _
    (witnessGenerator_isSelfAdjoint ψ coords d).isSymmetric

theorem signOperator_baseVector (ψ : X → ℝ) (g : X → Bool) :
    HilbertPointBridge.signOperator g (WeightedDualVectors.baseVector ψ) =
      WeightedDualVectors.weightedPoint ψ (fun x => (signTarget g x : ℂ)) := by
  ext x
  rw [HilbertPointBridge.signOperator_apply]
  simp only [WeightedDualVectors.baseVector, WeightedDualVectors.weightedPoint, PiLp.toLp_apply,
    mul_one]
  cases hg : g x <;> simp [HilbertPointBridge.signValue, signTarget, hg]

/-- Every failure of degree-(d-1) approximation yields a concrete Hermitian
polynomial-filtration matrix with a crossing norm greater than εd/2, together
with actual normalized true-fiber vectors exchanged at that norm. -/
theorem exists_degree_scale_witness (coords : X → σ → ℝ) (g : X → Bool)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 ≤ ε)
    (hno : ¬ ∃ p : MvPolynomial σ ℝ, p.totalDegree ≤ d - 1 ∧
      ∀ x, |signTarget g x - MvPolynomial.eval (coords x) p| ≤ ε) :
    ∃ (ψ : X → ℝ) (u : Bool → X → ℂ),
      (∑ x, |ψ x|) = 1 ∧
      ε * (d : ℝ) / 2 < ‖witnessStrip ψ coords g d‖ ∧
      0 < ‖witnessStrip ψ coords g d‖ ∧
      (∀ b, ∑ x, ‖u b x‖ ^ 2 = 1) ∧
      (∀ b x, u b x ≠ 0 → g x = b) ∧
      (∀ b x, ∑ y, LocalCommutation.innerCrossing g (witnessMatrix ψ coords d) x y * u b y =
        (‖witnessStrip ψ coords g d‖ : ℂ) * u (!b) x) := by
  obtain ⟨ψ, hmass, hvnorm, hhnorm, hvtop, horth, hcorr⟩ :=
    WeightedDualVectors.exists_weighted_polynomial_dual coords (signTarget g) (d - 1) ε hε hno
  let V : Fin d → Submodule ℂ (EuclideanSpace ℂ X) :=
    fun j => WeightedDualVectors.polynomialSpace ψ coords j.val
  have hv : ∀ j, WeightedDualVectors.baseVector ψ ∈ V j :=
    fun j => WeightedDualVectors.baseVector_mem ψ coords j.val
  have hh : ∀ j, WeightedDualVectors.dualVector ψ ∈ (V j)ᗮ := by
    intro j
    apply (V j).mem_orthogonal' _ |>.mpr
    intro w hw
    exact horth w (WeightedDualVectors.polynomialSpace_mono ψ coords (by omega) hw)
  have hcorr' : ε < (inner ℂ (WeightedDualVectors.dualVector ψ)
      (HilbertPointBridge.signOperator g (WeightedDualVectors.baseVector ψ))).re := by
    rwa [signOperator_baseVector]
  have hscale : ε * (d : ℝ) / 2 < ‖witnessStrip ψ coords g d‖ :=
    FiltrationOperator.generator_crossing_norm_gt d hd V (HilbertPointBridge.signOperator g)
      (HilbertPointBridge.signOperator_isSelfAdjoint g) (HilbertPointBridge.signOperator_involution g)
      (WeightedDualVectors.baseVector ψ) (WeightedDualVectors.dualVector ψ)
      hvnorm hhnorm hv hh ε hcorr'
  have hpos : 0 < ‖witnessStrip ψ coords g d‖ :=
    lt_of_le_of_lt (by positivity) hscale
  obtain ⟨u, hunorm, husupp, huex⟩ :=
    HilbertPointBridge.exists_point_exchange_for_crossingStrip g (witnessGenerator ψ coords d)
      (witnessGenerator_isSelfAdjoint ψ coords d) (norm_pos_iff.mp hpos)
  exact ⟨ψ, u, hmass, hscale, hpos, hunorm, husupp, huex⟩

end

end ApproxDegree.DegreeScaleWitness
end


