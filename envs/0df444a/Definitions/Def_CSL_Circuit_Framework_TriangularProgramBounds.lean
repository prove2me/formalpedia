-- Prove2me | Definitions.Def_CSL_Circuit_Framework_TriangularProgramBounds
-- name    : CSL_Circuit_Framework_TriangularProgramBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:23:22.564881+00:00
-- url     : https://prove2.me/theorems/0c737770-5653-4e8b-bcf9-4c501ec768e5
-- title:
--   Coded sorting library: Circuit / Framework / TriangularProgramBounds
-- statement:
--   Module `CodedSorting.Circuit.Framework.TriangularProgramBounds` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Actual finite pass programs for the fixed rational lower-triangular
--   coordinate changes. Their primitives retain buffered-read/write or aligned
--   block-transfer evidence through ScanProgram.Execution.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.TriangularProgramBounds

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Indexing_LexBlocks
import Definitions.Def_CSL_Shared_Programs_RationalScalar
open scoped Fin.NatCast Fin.IntCast Fin.CommRing

section TriangularRealization
/-! Actual finite pass programs for the fixed rational lower-triangular
coordinate changes. Their primitives retain buffered-read/write or aligned
block-transfer evidence through ScanProgram.Execution. -/

namespace CSL.TriangularRealization

open TriangularStreams LexBlocks FieldReflection ScanProgram
open SequentialArithmetic AffineStreams CoordinateScans MatrixFactorization

variable {m Q K : ℕ}

noncomputable def coordinatePass (i : Fin m)
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) (he : PrefixDependent i e)
    (key : (Fin m → Fin Q) → Fin Q → Fin K) (hk : PrefixDependent i key)
    (hinc : ∀ x a b, a < b → key x a = key x b → e x a < e x b) : Pass (Q^m) :=
  .streams K (coordinatePermutation i e he) (coordinateKey i key)
    (coordinatePermutation_increasing i e he key hk hinc)

noncomputable def multiplyPass {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hc : a.Coprime Q) (i : Fin m) : Pass (Q^m) :=
  coordinatePass i (fun _ => multiplicationEquiv hQ hc) (fun _ _ _ => rfl)
    (fun _ => multiplicationRun ha hQ) (fun _ _ _ => rfl)
    (fun _ x y hxy hr => multiplication_increasing_in_run ha hQ x y hxy hr)

noncomputable def inverseMultiplyPass {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hc : a.Coprime Q) (i : Fin m) : Pass (Q^m) :=
  coordinatePass i (fun _ => (multiplicationEquiv hQ hc).symm) (fun _ _ _ => rfl)
    (fun _ x => multiplicationRun ha hQ ((multiplicationEquiv hQ hc).symm x))
    (fun _ _ _ => rfl)
    (fun _ => inverse_increasing_streams _ _
      (fun x y hxy hr => multiplication_increasing_in_run ha hQ x y hxy hr))

noncomputable def addPass (i : Fin m) (offset : (Fin m → Fin Q) → Fin Q)
    (ho : PrefixDependent i offset) : Pass (Q^m) :=
  coordinatePass i (fun x => additionEquiv (offset x))
    (fun x y hp => congrArg additionEquiv (ho x y hp))
    (fun x => additionRun (offset x))
    (fun x y hp => congrArg additionRun (ho x y hp))
    (fun x a b hab hr => addition_increasing_in_run (offset x) a b hab hr)

/-- These are actual two block-reflection primitives, not a reverse-reader oracle. -/
def reflectionPasses (i : Fin m) (hQ : 0 < Q) : List (Pass (Q^m)) :=
  [.reverse (PrefixCount Q i) (Q*SuffixCount Q i) (Nat.mul_pos hQ (pow_pos hQ _))
      (blockCard i),
   .reverse (PrefixCount Q i*Q) (SuffixCount Q i) (pow_pos hQ _)
      ((Nat.mul_assoc _ _ _).trans (blockCard i))]

theorem reflection_destination (i : Fin m) (hQ : 0 < Q) :
    destination (reflectionPasses i hQ) =
      coordinatePermutation i (fun _ => Fin.revPerm) (fun _ _ _ => rfl) := by
  apply Equiv.ext
  intro y
  let h := blockCard (Q := Q) i
  obtain ⟨z,rfl⟩ := (finCongr h).surjective y
  change reversePerm (PrefixCount Q i*Q) (SuffixCount Q i) _
      (reversePerm (PrefixCount Q i) (Q*SuffixCount Q i) h (finCongr h z)) = _
  have hfirst : reversePerm (PrefixCount Q i) (Q*SuffixCount Q i) h (finCongr h z) =
      finCongr h (BlockReflection.segmentReverseEquiv _ _ z) := by
    simp [reversePerm]
  rw [hfirst]
  have hsecond (w : Fin (PrefixCount Q i*(Q*SuffixCount Q i))) :
      reversePerm (PrefixCount Q i*Q) (SuffixCount Q i)
        ((Nat.mul_assoc _ _ _).trans h) (finCongr h w) =
      finCongr h (suffixReverse w) := rfl
  rw [hsecond]
  have hpair := congrArg (fun e : Equiv.Perm (Fin (PrefixCount Q i*(Q*SuffixCount Q i))) => e z)
    (two_reversals (P := PrefixCount Q i) (Q := Q) (S := SuffixCount Q i))
  change suffixReverse (BlockReflection.segmentReverseEquiv _ _ z) = _ at hpair
  rw [hpair]
  exact blockFieldPermutation i Fin.revPerm (finCongr h z)

section FinRing

variable [NeZero Q]

theorem multiplication_eq_ring {a : ℕ} (hQ : 0 < Q) (hc : a.Coprime Q) (x : Fin Q) :
    multiplicationEquiv hQ hc x = (a : Fin Q) * x := by
  apply Fin.ext
  simp [multiply,Fin.val_mul,Nat.mod_mul_right_mod]

@[simp] theorem multiplyPass_encoded {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hc : a.Coprime Q) (i : Fin m) (x : Fin m → Fin Q) :
    (multiplyPass ha hQ hc i).permutation (lexLayout x) =
      lexLayout (scaleCoordinate (a : Fin Q) i x) := by
  change coordinatePermutation i (fun _ => multiplicationEquiv hQ hc)
    (fun _ _ _ => rfl) (lexLayout x) = _
  rw [coordinatePermutation_encoded,multiplication_eq_ring]
  rfl

@[simp] theorem addPass_encoded (i : Fin m) (offset : (Fin m → Fin Q) → Fin Q)
    (ho : PrefixDependent i offset) (x : Fin m → Fin Q) :
    (addPass i offset ho).permutation (lexLayout x) =
      lexLayout (Function.update x i (x i+offset x)) := by
  change coordinatePermutation i (fun x => additionEquiv (offset x)) _ (lexLayout x) = _
  rw [coordinatePermutation_encoded,additionEquiv_apply_add]

noncomputable def negationPasses (i : Fin m) (hQ : 0 < Q) : List (Pass (Q^m)) :=
  reflectionPasses i hQ ++ [addPass i (fun _ => 1) (fun _ _ _ => rfl)]

theorem destination_append (xs ys : List (Pass (Q^m))) :
    destination (xs++ys) = (destination xs).trans (destination ys) := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append,destination,ih]; rfl

theorem negation_destination (i : Fin m) (hQ : 0 < Q) (x : Fin m → Fin Q) :
    destination (negationPasses i hQ) (lexLayout x) =
      lexLayout (Function.update x i (-x i)) := by
  rw [negationPasses,destination_append,Equiv.trans_apply,reflection_destination,
    coordinatePermutation_encoded]
  change (addPass i (fun _ => 1) (fun _ _ _ => rfl)).permutation
    (lexLayout (Function.update x i (x i).rev)) = _
  rw [addPass_encoded,Function.update_self]
  have hneg : (x i).rev+1 = -x i := by
    simpa using reverse_add_offset (0 : Fin Q) (x i)
  rw [hneg,Function.update_idem]

/-- A signed fixed integer uses a positive multiplier and, only if negative,
the proved physical reflection-plus-addition program. -/
noncomputable def signedMultiplyPasses (z : ℤ) (hz : z ≠ 0) (hc : z.natAbs.Coprime Q)
    (i : Fin m) (hQ : 0 < Q) : List (Pass (Q^m)) :=
  [multiplyPass (Int.natAbs_pos.mpr hz) hQ hc i] ++
    if 0 ≤ z then [] else negationPasses i hQ

theorem signedMultiply_destination (z : ℤ) (hz : z ≠ 0) (hc : z.natAbs.Coprime Q)
    (i : Fin m) (hQ : 0 < Q) (x : Fin m → Fin Q) :
    destination (signedMultiplyPasses z hz hc i hQ) (lexLayout x) =
      lexLayout (scaleCoordinate (z : Fin Q) i x) := by
  rw [signedMultiplyPasses,destination_append,Equiv.trans_apply]
  change destination (if 0 ≤ z then [] else negationPasses i hQ)
    ((multiplyPass (Int.natAbs_pos.mpr hz) hQ hc i).permutation (lexLayout x)) = _
  rw [multiplyPass_encoded]
  cases z with
  | ofNat n => simp [destination,scaleCoordinate]
  | negSucc n =>
    rw [if_neg (by omega),negation_destination]
    simp only [scaleCoordinate,Function.update_self,Function.update_idem,
      Int.natAbs_negSucc,Int.cast_negSucc,neg_mul]

theorem inverseMultiply_encoded {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hc : a.Coprime Q) (i : Fin m) (x : Fin m → Fin Q) :
    (inverseMultiplyPass ha hQ hc i).permutation (lexLayout x) =
      lexLayout (Function.update x i ((multiplicationEquiv hQ hc).symm (x i))) := by
  exact coordinatePermutation_encoded i _ _ x

/-- A relation d*c=n is enough to prove the exact effect of the fixed
numerator and inverse-denominator passes; c is the already-specialized value. -/
theorem signed_fraction_destination (z : ℤ) (hz : z ≠ 0) (d : ℕ) (hd : 0 < d)
    (hzc : z.natAbs.Coprime Q) (hdc : d.Coprime Q) (c : Fin Q)
    (hfrac : (d : Fin Q)*c = (z : Fin Q)) (i : Fin m) (hQ : 0 < Q)
    (x : Fin m → Fin Q) :
    destination (signedMultiplyPasses z hz hzc i hQ ++ [inverseMultiplyPass hd hQ hdc i])
      (lexLayout x) = lexLayout (scaleCoordinate c i x) := by
  rw [destination_append,Equiv.trans_apply,signedMultiply_destination]
  change (inverseMultiplyPass hd hQ hdc i).permutation
    (lexLayout (scaleCoordinate (z : Fin Q) i x)) = _
  rw [inverseMultiply_encoded]
  simp only [scaleCoordinate,Function.update_self,Function.update_idem]
  apply congrArg lexLayout
  apply congrArg (Function.update x i)
  apply (multiplicationEquiv hQ hdc).injective
  rw [Equiv.apply_symm_apply,multiplication_eq_ring,← mul_assoc,hfrac]

/-- Fixed integer data for the diagonal; the equality is in the actual modulus. -/
structure DiagonalFractions (A : Matrix (Fin m) (Fin m) (Fin Q)) where
  numerator : Fin m → ℤ
  denominator : Fin m → ℕ
  numerator_ne_zero : ∀ i, numerator i ≠ 0
  denominator_pos : ∀ i, 0 < denominator i
  numerator_coprime : ∀ i, (numerator i).natAbs.Coprime Q
  denominator_coprime : ∀ i, (denominator i).Coprime Q
  fraction : ∀ i, (denominator i : Fin Q) * A i i = (numerator i : Fin Q)

noncomputable def rowPasses (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (i : Fin m) (hQ : 0 < Q) : List (Pass (Q^m)) :=
  signedMultiplyPasses (D.numerator i) (D.numerator_ne_zero i)
    (D.numerator_coprime i) i hQ ++
    [inverseMultiplyPass (D.denominator_pos i) hQ (D.denominator_coprime i) i] ++
    [addPass i (prefixOffset A i)
      (fun x y hp => prefixOffset_depends_only_on_prefix A i x y hp)]

theorem rowPasses_destination (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (hA : TriangularProgram.lower A)
    (i : Fin m) (hQ : 0 < Q) (x : Fin m → Fin Q) :
    destination (rowPasses A D i hQ) (lexLayout x) =
      lexLayout (TriangularProgram.updateCoordinate A i x) := by
  rw [rowPasses,destination_append,Equiv.trans_apply]
  rw [signed_fraction_destination _ _ _ _ _ _ _ (D.fraction i)]
  change (addPass i (prefixOffset A i)
    (fun x y hp => prefixOffset_depends_only_on_prefix A i x y hp)).permutation
    (lexLayout (scaleCoordinate (A i i) i x)) = _
  rw [addPass_encoded]
  change lexLayout (addPrefixCoordinate A i (scaleCoordinate (A i i) i x)) = _
  rw [scalar_steps_eq_update A hA]

noncomputable def descendingPasses (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (hQ : 0 < Q) : (n : ℕ) → n ≤ m → List (Pass (Q^m))
  | 0,_ => []
  | n+1,hn => rowPasses A D ⟨n,by omega⟩ hQ ++ descendingPasses A D hQ n (by omega)

theorem descendingPasses_destination (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (hA : TriangularProgram.lower A) (hQ : 0 < Q)
    (n : ℕ) (hn : n ≤ m) (x : Fin m → Fin Q) :
    destination (descendingPasses A D hQ n hn) (lexLayout x) =
      lexLayout (TriangularProgram.descending A n hn x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [descendingPasses,destination_append,Equiv.trans_apply,rowPasses_destination A D hA]
    exact ih _ _

/-- The concrete pass list computes the entire matrix action in one common layout. -/
theorem complete_destination (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (hA : TriangularProgram.lower A) (hQ : 0 < Q)
    (x : Fin m → Fin Q) :
    destination (descendingPasses A D hQ m (Nat.le_refl m)) (lexLayout x) =
      lexLayout (A.mulVec x) := by
  rw [descendingPasses_destination A D hA]
  exact congrArg lexLayout (TriangularProgram.execute_eq_mulVec A hA x)

@[simp] theorem totalConstant_append (xs ys : List (Pass (Q^m))) :
    totalConstant (xs++ys) = totalConstant xs+totalConstant ys := by
  simp [totalConstant,List.map_append,List.sum_append]

theorem signedMultiply_constant (z : ℤ) (hz : z ≠ 0) (hc : z.natAbs.Coprime Q)
    (i : Fin m) (hQ : 0 < Q) :
    totalConstant (signedMultiplyPasses z hz hc i hQ) ≤ 2*z.natAbs+26 := by
  unfold signedMultiplyPasses
  rw [totalConstant_append]
  by_cases hp : 0 ≤ z
  · simp [hp,totalConstant,multiplyPass,coordinatePass,Pass.constant]
  · simp [hp,negationPasses,reflectionPasses,totalConstant,multiplyPass,coordinatePass,
      addPass,Pass.constant]

/-- This bound depends on fixed integer numerator/denominator data alone. -/
def coefficientConstant {A : Matrix (Fin m) (Fin m) (Fin Q)} (D : DiagonalFractions A) : ℕ :=
  ∑ i, (2*(D.numerator i).natAbs+2*D.denominator i+42)

theorem rowPasses_constant (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (i : Fin m) (hQ : 0 < Q) :
    totalConstant (rowPasses A D i hQ) ≤ coefficientConstant D := by
  have hs := signedMultiply_constant (D.numerator i) (D.numerator_ne_zero i)
    (D.numerator_coprime i) i hQ
  have hrow : totalConstant (rowPasses A D i hQ) ≤
      2*(D.numerator i).natAbs+2*D.denominator i+42 := by
    simp only [rowPasses,totalConstant_append]
    simp only [totalConstant,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      inverseMultiplyPass,coordinatePass,addPass,Pass.constant]
    simp only [totalConstant] at hs
    omega
  apply hrow.trans
  unfold coefficientConstant
  exact Finset.single_le_sum
    (f := fun j : Fin m => 2*(D.numerator j).natAbs+2*D.denominator j+42)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem descendingPasses_constant (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (hQ : 0 < Q) (n : ℕ) (hn : n ≤ m) :
    totalConstant (descendingPasses A D hQ n hn) ≤ n*coefficientConstant D := by
  induction n with
  | zero => simp [descendingPasses,totalConstant]
  | succ n ih =>
    rw [descendingPasses,totalConstant_append,Nat.add_mul,Nat.one_mul]
    exact (Nat.add_le_add (rowPasses_constant A D _ hQ) (ih (by omega))).trans_eq (Nat.add_comm _ _)

/-- Actual execution and actual total transfer bound for the complete pass list. -/
theorem complete_execution {Value : Type*} [Inhabited Value]
    (A : Matrix (Fin m) (Fin m) (Fin Q)) (D : DiagonalFractions A)
    (hQ : 0 < Q) (F : Fin (Q^m) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB (descendingPasses A D hQ m (Nat.le_refl m)) F cost ∧
      cost ≤ (m*coefficientConstant D)*(Q^m/B+1) := by
  obtain ⟨cost,he,hc⟩ := program_correct (descendingPasses A D hQ m (Nat.le_refl m)) F B hB
  refine ⟨cost,he,hc.trans ?_⟩
  exact Nat.mul_le_mul_right _ (descendingPasses_constant A D hQ m (Nat.le_refl m))

end FinRing

end CSL.TriangularRealization
end TriangularRealization

section SpecializedTriangular
/-! The fixed rational numerator/denominator data are instantiated from the
same joint specialization already used by the network and its edge factors. -/

namespace CSL.SpecializedTriangular

open MatrixFactorization TriangularStreams TriangularRealization ScanProgram

variable {Family : Type*} [Fintype Family] {m : ℕ}
variable {A : Family → Matrix (Fin m) (Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ)

local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

noncomputable def finMatrix (k : Family) : Matrix (Fin m) (Fin m) (Fin (F.prime^f)) :=
  (F.matrix f k).map (ZMod.finEquiv (F.prime^f)).symm

noncomputable def diagonalData (k : Family) (hdiag : ∀ i, A k i i ≠ 0) :
    DiagonalFractions (finMatrix F f k) where
  numerator i := (A k i i).num
  denominator i := (A k i i).den
  numerator_ne_zero i := Rat.num_ne_zero.mpr (hdiag i)
  denominator_pos i := Nat.pos_of_ne_zero (A k i i).den_nz
  numerator_coprime i := RationalScalar.numerator_coprime F k i i (hdiag i) f
  denominator_coprime i := RationalScalar.denominator_coprime F k i i f
  fraction i := by
    have h := congrArg (ZMod.finEquiv (F.prime^f)).symm
      (RationalScalar.reduced_denominator_identity F k i i f)
    simpa only [map_mul,map_natCast,map_intCast,finMatrix,Matrix.map_apply] using h

theorem finMatrix_lower (k : Family) (hA : LowerTriangular (A k)) :
    TriangularProgram.lower (finMatrix F f k) := by
  intro i j hij
  change (ZMod.finEquiv (F.prime^f)).symm (F.matrix f k i j) = 0
  rw [F.preserves_lower_triangular k hA f i j hij,map_zero]

/-- Invertibility and triangularity imply the needed nonzero diagonal;
this is not an additional algorithmic assumption on the chosen factors. -/
theorem diagonal_nonzero (M : Matrix (Fin m) (Fin m) ℚ)
    (hM : LowerTriangular M) (hU : IsUnit M) : ∀ i, M i i ≠ 0 := by
  have hd : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp hU |>.ne_zero
  have htri : M.BlockTriangular (OrderDual.toDual : Fin m → OrderDual (Fin m)) :=
    fun {_ _} hij => hM _ _ hij
  rw [Matrix.det_of_lowerTriangular M htri] at hd
  intro i
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)

noncomputable def program (k : Family) (hdiag : ∀ i, A k i i ≠ 0) :
    List (Pass ((F.prime^f)^m)) :=
  descendingPasses (finMatrix F f k) (diagonalData F f k hdiag)
    (pow_pos F.prime_is_prime.pos _) m (Nat.le_refl m)

/-- A single finite rational constant works for every power of the same prime. -/
def fixedConstant (k : Family) : ℕ :=
  m * ∑ i, (2*(A k i i).num.natAbs+2*(A k i i).den+42)

theorem program_destination (k : Family) (hdiag : ∀ i, A k i i ≠ 0)
    (hA : LowerTriangular (A k)) (x : Fin m → Fin (F.prime^f)) :
    destination (program F f k hdiag) (lexLayout x) =
      lexLayout ((finMatrix F f k).mulVec x) :=
  complete_destination _ _ (finMatrix_lower F f k hA) _ x

/-- The matrix in the implemented address map is precisely the reduced
joint-family matrix, transported only by Fin Q ≃+* ZMod Q. -/
theorem matrix_semantics (k : Family) (x : Fin m → Fin (F.prime^f)) (i : Fin m) :
    ZMod.finEquiv (F.prime^f) ((finMatrix F f k).mulVec x i) =
      (F.matrix f k).mulVec (fun j => ZMod.finEquiv (F.prime^f) (x j)) i := by
  change (ZMod.finEquiv (F.prime^f)).toRingHom ((finMatrix F f k).mulVec x i) = _
  rw [(ZMod.finEquiv (F.prime^f)).toRingHom.map_mulVec]
  have hm : (finMatrix F f k).map (ZMod.finEquiv (F.prime^f)).toRingHom = F.matrix f k := by
    ext a b
    exact (ZMod.finEquiv (F.prime^f)).apply_symm_apply _
  rw [hm]
  rfl

/-- Every step has physical buffered/block execution evidence. Neither the
prime nor its exponent changes the fixed rational constant. -/
theorem program_execution {Value : Type*} [Inhabited Value]
    (k : Family) (hdiag : ∀ i, A k i i ≠ 0)
    (input : Fin ((F.prime^f)^m) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB (program F f k hdiag) input cost ∧
      cost ≤ fixedConstant (A := A) k * ((F.prime^f)^m/B+1) := by
  simpa only [program,fixedConstant,coefficientConstant,diagonalData] using
    complete_execution (finMatrix F f k) (diagonalData F f k hdiag)
      (pow_pos F.prime_is_prime.pos _) input B hB

end CSL.SpecializedTriangular
end SpecializedTriangular

section GlobalTriangular
/-! The complete common-prime triangular program on a middle vector field,
shared across arbitrary outer prefixes and suffixes. -/

namespace CSL.GlobalTriangular

open MatrixFactorization TriangularStreams TriangularRealization ScanProgram
open ScanProgramLift SpecializedTriangular

variable {Family : Type*} [Fintype Family] {m : ℕ}
variable {A : Family → Matrix (Fin m) (Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ)

local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

noncomputable def program (k : Family) (hdiag : ∀ i, A k i i ≠ 0)
    (P S : ℕ) (hS : 0 < S) : List (Pass (P*((F.prime^f)^m*S))) :=
  liftProgram P S hS (SpecializedTriangular.program F f k hdiag)

/-- The prefix and suffix are unchanged, and the entire vector field is
multiplied by the jointly-specialized matrix. -/
theorem destination_encoded (k : Family) (hdiag : ∀ i, A k i i ≠ 0)
    (hA : LowerTriangular (A k)) (P S : ℕ) (hS : 0 < S)
    (p : Fin P) (x : Fin m → Fin (F.prime^f)) (s : Fin S) :
    destination (program F f k hdiag P S hS) (tripleEncode (p,lexLayout x,s)) =
      tripleEncode (p,lexLayout ((finMatrix F f k).mulVec x),s) := by
  rw [program,liftProgram_destination,globalFieldEquiv_encoded,
    SpecializedTriangular.program_destination F f k hdiag hA]

theorem program_constant (k : Family) (hdiag : ∀ i, A k i i ≠ 0)
    (P S : ℕ) (hS : 0 < S) :
    totalConstant (program F f k hdiag P S hS) ≤
      2*fixedConstant (A := A) k := by
  apply (liftProgram_constant P S hS _).trans
  apply Nat.mul_le_mul_left 2
  simpa only [SpecializedTriangular.program,fixedConstant,coefficientConstant,diagonalData] using
    descendingPasses_constant (finMatrix F f k) (diagonalData F f k hdiag)
      (pow_pos F.prime_is_prime.pos _) m (Nat.le_refl m)

/-- The constant is independent of f, P, S and the file/block lengths.
Each primitive includes its physical disk-to-disk execution evidence. -/
theorem execution {Value : Type*} [Inhabited Value]
    (k : Family) (hdiag : ∀ i, A k i i ≠ 0) (P S : ℕ) (hS : 0 < S)
    (input : Fin (P*((F.prime^f)^m*S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB (program F f k hdiag P S hS) input cost ∧
      cost ≤ (2*fixedConstant (A := A) k)*(P*((F.prime^f)^m*S)/B+1) := by
  obtain ⟨cost,he,hc⟩ := program_correct (program F f k hdiag P S hS) input B hB
  exact ⟨cost,he,hc.trans (Nat.mul_le_mul_right _ (program_constant F f k hdiag P S hS))⟩

/-- The same finite constant bounds the resident block count of every pass;
passes run sequentially and reuse those buffers. -/
theorem peak_buffers (k : Family) (hdiag : ∀ i, A k i i ≠ 0)
    (P S : ℕ) (hS : 0 < S) (B : ℕ)
    (p : Pass (P*((F.prime^f)^m*S))) (hp : p ∈ program F f k hdiag P S hS) :
    p.buffers*B ≤ (2*fixedConstant (A := A) k)*B := by
  exact Nat.mul_le_mul_right B
    ((member_buffers_le_total _ p hp).trans (program_constant F f k hdiag P S hS))

/-- The caller supplies only the proved rational factor properties; diagonal
nonvanishing and every finite-stream implementation are obtained internally. -/
theorem lower_unit_implementation {Value : Type*} [Inhabited Value]
    (k : Family) (hA : LowerTriangular (A k)) (hu : IsUnit (A k))
    (P S : ℕ) (hS : 0 < S) (input : Fin (P*((F.prime^f)^m*S)) → Value)
    (B : ℕ) (hB : 0 < B) :
    let ps := program F f k (diagonal_nonzero (A k) hA hu) P S hS
    (∀ (p : Fin P) (x : Fin m → Fin (F.prime^f)) (s : Fin S),
      destination ps (tripleEncode (p,lexLayout x,s)) =
        tripleEncode (p,lexLayout ((finMatrix F f k).mulVec x),s)) ∧
    ∃ cost, Execution B hB ps input cost ∧
      cost ≤ (2*fixedConstant (A := A) k)*(P*((F.prime^f)^m*S)/B+1) := by
  exact ⟨destination_encoded F f k _ hA P S hS,
    execution F f k _ P S hS input B hB⟩

end CSL.GlobalTriangular
end GlobalTriangular

section TriangularProgramBounds
/-! Fixed public program-counter bounds for the concrete triangular programs. -/

namespace CSL.TriangularProgramBounds

open TriangularRealization ScanProgram ScanProgramLift

variable {m Q : ℕ} [NeZero Q]

theorem signed_length (z : ℤ) (hz : z ≠ 0) (hc : z.natAbs.Coprime Q)
    (i : Fin m) (hQ : 0 < Q) :
    (signedMultiplyPasses z hz hc i hQ).length ≤ 4 := by
  simp only [signedMultiplyPasses,List.length_append,List.length_cons,List.length_nil]
  split_ifs <;> simp [negationPasses,reflectionPasses]

theorem row_length (A : Matrix (Fin m) (Fin m) (Fin Q)) (D : DiagonalFractions A)
    (i : Fin m) (hQ : 0 < Q) : (rowPasses A D i hQ).length ≤ 6 := by
  have h := signed_length (D.numerator i) (D.numerator_ne_zero i)
    (D.numerator_coprime i) i hQ
  simp only [rowPasses,List.length_append,List.length_cons,List.length_nil]
  omega

theorem descending_length (A : Matrix (Fin m) (Fin m) (Fin Q))
    (D : DiagonalFractions A) (hQ : 0 < Q) (n : ℕ) (hn : n ≤ m) :
    (descendingPasses A D hQ n hn).length ≤ 6*n := by
  induction n with
  | zero => simp [descendingPasses]
  | succ n ih =>
    simp only [descendingPasses,List.length_append,Nat.mul_add,Nat.mul_one]
    have h := row_length A D ⟨n,by omega⟩ hQ
    have hi := ih (by omega)
    omega

theorem lift_pass_length {V : ℕ} (P S : ℕ) (hS : 0 < S) (p : Pass V) :
    (liftPass P S hS p).length ≤ 2 := by
  cases p <;> simp [liftPass,fieldReflections]

theorem lift_program_length {V : ℕ} (P S : ℕ) (hS : 0 < S) (ps : List (Pass V)) :
    (liftProgram P S hS ps).length ≤ 2*ps.length := by
  induction ps with
  | nil => simp [liftProgram]
  | cons p ps ih =>
    change (liftPass P S hS p ++ liftProgram P S hS ps).length ≤ _
    simp only [List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    have hp := lift_pass_length P S hS p
    omega

section Specialization

open MatrixFactorization SpecializedTriangular
variable {Family : Type*} [Fintype Family]
variable {A : Family → Matrix (Fin m) (Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ)
local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

/-- A fixed number of public pass-control states, independent of file size,
modulus exponent, prefix count and suffix size. -/
theorem global_length (k : Family) (hdiag : ∀ i, A k i i ≠ 0)
    (P S : ℕ) (hS : 0 < S) :
    (GlobalTriangular.program F f k hdiag P S hS).length ≤ 12*m := by
  have hl := lift_program_length P S hS (SpecializedTriangular.program F f k hdiag)
  have hc := descending_length (finMatrix F f k) (diagonalData F f k hdiag)
    (pow_pos F.prime_is_prime.pos _) m (Nat.le_refl m)
  change (SpecializedTriangular.program F f k hdiag).length ≤ 6*m at hc
  change (GlobalTriangular.program F f k hdiag P S hS).length ≤
    2*(SpecializedTriangular.program F f k hdiag).length at hl
  omega

end Specialization
end CSL.TriangularProgramBounds
end TriangularProgramBounds


