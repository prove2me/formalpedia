-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchangeCost
-- name    : CSL_Interchange_Framework_Recursion_RecursiveExchangeCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:01:42.160801+00:00
-- url     : https://prove2.me/theorems/12d12924-4b44-454b-a88a-9bb35944a7f1
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / RecursiveExchangeCost
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.RecursiveExchangeCost` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The actual jointly specialized edge factors, without choosing a new prime,
--   consume the proved global triangular stream implementation.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.RecursiveExchangeCost

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchange
import Definitions.Def_CSL_Circuit_Framework_TriangularProgramBounds
import Definitions.Def_CSL_Interchange_Framework_Fields_BinaryPaddingScan
import Mathlib.Data.Finset.Sort

/-! The actual jointly specialized edge factors, without choosing a new prime,
consume the proved global triangular stream implementation. -/
set_option maxRecDepth 4096
set_option autoImplicit false

namespace CSL.RecursiveExchangeCost
open MatrixFactorization RecursiveExchange ScanProgram
open scoped BigOperators
noncomputable section
local instance : LinearOrder Index := RecursiveExchange.indexOrder
local instance : LE Index := RecursiveExchange.indexOrder.toLE
local instance : LT Index := RecursiveExchange.indexOrder.toLT

section Reindex
variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K]
variable {A : K → Matrix I I ℚ}

/-- Only coordinate names change. The denominator, prime and reduction maps
are the same objects already chosen for the entire network family. -/
@[reducible] def reindexFamily (F : SpecializedFamily A) (e : J ≃ I) :
    SpecializedFamily (fun k j l => A k (e j) (e l)) where
  denominator := F.denominator
  denominator_ne_zero := F.denominator_ne_zero
  prime := F.prime
  prime_is_prime := F.prime_is_prime
  prime_is_odd := F.prime_is_odd
  coefficients k j l := F.coefficients k (e j) (e l)
  lift_correct k := by ext j l; exact congrArg (fun M => M (e j) (e l)) (F.lift_correct k)
  inverse_coefficients k j l := F.inverse_coefficients k (e j) (e l)
  inverse_lift_correct k j l := F.inverse_lift_correct k (e j) (e l)
  reduce := F.reduce

omit [Fintype K] in
theorem reindex_matrix (F : SpecializedFamily A) (e : J ≃ I)
    (f : ℕ) (k : K) (j l : J) :
    (reindexFamily F e).matrix f k j l = F.matrix f k (e j) (e l) := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem reindex_lower [LinearOrder I] [LinearOrder J] (e : J ≃o I)
    (M : Matrix I I ℚ) (hM : LowerTriangular M) :
    LowerTriangular (fun i j => M (e i) (e j)) := by
  intro i j hij
  exact hM _ _ (e.strictMono hij)

theorem reindex_unit (e : J ≃ I) (M : Matrix I I ℚ) (hM : IsUnit M) :
    IsUnit (show Matrix J J ℚ from fun i j => M (e i) (e j)) := by
  have h := hM.map (Matrix.reindexAlgEquiv ℚ ℚ e.symm).toMonoidHom
  exact h

end Reindex

def indexEnumeration : Fin Parameters.m ≃o Index :=
  Fintype.orderIsoFinOfCardEq Index StageLabels.actual_matrix_card

abbrev Family := (Node ⊕ Edge) × Fin 6

def matrices : Family → Matrix (Fin Parameters.m) (Fin Parameters.m) ℚ :=
  fun k i j => expandedFamily rationalFamily uniform.data k (indexEnumeration i) (indexEnumeration j)

abbrev sharedSpecialization : SpecializedFamily matrices :=
  reindexFamily uniform.specialization indexEnumeration.toEquiv

theorem same_prime : sharedSpecialization.prime = radix := rfl

local instance sharedPowerNeZero (f : ℕ) : NeZero (sharedSpecialization.prime ^ f) :=
  ⟨pow_ne_zero _ sharedSpecialization.prime_is_prime.ne_zero⟩

theorem matrix_agrees (f : ℕ) (k : Node ⊕ Edge) (slot : Fin 6) (i j : Fin Parameters.m) :
    sharedSpecialization.matrix f (k, slot) i j =
      uniform.matrix f k slot (indexEnumeration i) (indexEnumeration j) := rfl

/-- The four coordinate changes surrounding each edge's sparse recursion. -/
inductive Factor where
  | left | right | leftInverse | rightInverse
  deriving DecidableEq

instance : Fintype Factor :=
  ⟨{Factor.left, Factor.right, Factor.leftInverse, Factor.rightInverse},
    by intro x; cases x <;> simp⟩

def Factor.slot : Factor → Fin 6
  | .left => 1
  | .right => 3
  | .leftInverse => 4
  | .rightInverse => 5

def factorKey (e : Edge) (a : Factor) : Family := (.inr e, a.slot)

theorem rational_factor_lower (e : Edge) (a : Factor) :
    LowerTriangular (expandedFamily rationalFamily uniform.data (factorKey e a)) := by
  cases a with
  | left => simpa [factorKey, Factor.slot, expandedFamily] using (uniform.data (.inr e)).left_lower
  | right => simpa [factorKey, Factor.slot, expandedFamily] using (uniform.data (.inr e)).right_lower
  | leftInverse => simpa [factorKey, Factor.slot, expandedFamily] using
      (uniform.data (.inr e)).left_lower.inv (uniform.data (.inr e)).left_unit
  | rightInverse => simpa [factorKey, Factor.slot, expandedFamily] using
      (uniform.data (.inr e)).right_lower.inv (uniform.data (.inr e)).right_unit

theorem rational_factor_unit (e : Edge) (a : Factor) :
    IsUnit (expandedFamily rationalFamily uniform.data (factorKey e a)) := by
  cases a with
  | left => simpa [factorKey, Factor.slot, expandedFamily] using (uniform.data (.inr e)).left_unit
  | right => simpa [factorKey, Factor.slot, expandedFamily] using (uniform.data (.inr e)).right_unit
  | leftInverse => simpa [factorKey, Factor.slot, expandedFamily] using
      Matrix.isUnit_nonsing_inv_iff.mpr (uniform.data (.inr e)).left_unit
  | rightInverse => simpa [factorKey, Factor.slot, expandedFamily] using
      Matrix.isUnit_nonsing_inv_iff.mpr (uniform.data (.inr e)).right_unit

theorem factor_lower (e : Edge) (a : Factor) : LowerTriangular (matrices (factorKey e a)) :=
  reindex_lower indexEnumeration _ (rational_factor_lower e a)

theorem factor_unit (e : Edge) (a : Factor) : IsUnit (matrices (factorKey e a)) :=
  reindex_unit indexEnumeration.toEquiv _ (rational_factor_unit e a)

def factorConstant (e : Edge) (a : Factor) : ℕ :=
  2 * SpecializedTriangular.fixedConstant (A := matrices) (factorKey e a)

def factorProgram (f : ℕ) (e : Edge) (a : Factor) (P S : ℕ) (hS : 0 < S) :
    List (Pass (P * ((radix ^ f) ^ Parameters.m * S))) :=
  GlobalTriangular.program sharedSpecialization f (factorKey e a)
    (SpecializedTriangular.diagonal_nonzero _ (factor_lower e a) (factor_unit e a)) P S hS

theorem factorProgram_constant (f : ℕ) (e : Edge) (a : Factor)
    (P S : ℕ) (hS : 0 < S) :
    totalConstant (factorProgram f e a P S hS) ≤ factorConstant e a :=
  GlobalTriangular.program_constant sharedSpecialization f (factorKey e a) _ P S hS

theorem factorProgram_execution {Value : Type*} [Inhabited Value]
    (f : ℕ) (e : Edge) (a : Factor) (P S : ℕ) (hS : 0 < S)
    (input : Fin (P * ((radix ^ f) ^ Parameters.m * S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB (factorProgram f e a P S hS) input cost ∧
      cost ≤ factorConstant e a * (P * ((radix ^ f) ^ Parameters.m * S) / B + 1) :=
  GlobalTriangular.execution sharedSpecialization f (factorKey e a) _ P S hS input B hB

/-- Field vectors use the same increasing index enumeration as the actual
rank factorization; coefficients are reduced by the same ring homomorphism. -/
def factorMatrix (f : ℕ) (e : Edge) (a : Factor) : Matrix Index Index (Scalar f) :=
  uniform.matrix f (.inr e) a.slot

def fieldVector (f : ℕ) (x : Field f) : Fin Parameters.m → Fin (radix ^ f) :=
  fun i => (ZMod.finEquiv (radix ^ f)).symm (x (indexEnumeration i))

theorem reindex_mulVec {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (e : J ≃ I) (M : Matrix I I R) (x : I → R) (i : J) :
    (show Matrix J J R from fun a b => M (e a) (e b)).mulVec (fun j => x (e j)) i =
      M.mulVec x (e i) := by
  exact Equiv.sum_comp e (fun j => M (e i) j * x j)

theorem fieldVector_mulVec (f : ℕ) (e : Edge) (a : Factor) (x : Field f) :
    (SpecializedTriangular.finMatrix sharedSpecialization f (factorKey e a)).mulVec
      (fieldVector f x) = fieldVector f ((factorMatrix f e a).mulVec x) := by
  funext i
  apply (ZMod.finEquiv (radix ^ f)).injective
  calc
    _ = (sharedSpecialization.matrix f (factorKey e a)).mulVec
        (fun j => x (indexEnumeration j)) i := by
      have h := SpecializedTriangular.matrix_semantics sharedSpecialization f (factorKey e a)
        (fieldVector f x) i
      simpa only [same_prime, fieldVector, RingEquiv.apply_symm_apply] using h
    _ = (factorMatrix f e a).mulVec x (indexEnumeration i) := by
      exact reindex_mulVec indexEnumeration.toEquiv (factorMatrix f e a) x i
    _ = _ := by simp only [fieldVector, RingEquiv.apply_symm_apply]

/-- The disk program applies exactly the original edge factor to the selected
whole vector, leaving the outer prefix and suffix fixed. -/
theorem factorProgram_destination_reduced (f : ℕ) (e : Edge) (a : Factor)
    (P S : ℕ) (hS : 0 < S) (p : Fin P) (x : Fin Parameters.m → Fin (radix ^ f)) (s : Fin S) :
    destination (factorProgram f e a P S hS)
        (TriangularStreams.tripleEncode (p, TriangularStreams.lexLayout x, s)) =
      TriangularStreams.tripleEncode (p, TriangularStreams.lexLayout
        ((SpecializedTriangular.finMatrix sharedSpecialization f (factorKey e a)).mulVec x), s) := by
  have hp : factorProgram f e a P S hS =
      GlobalTriangular.program sharedSpecialization f (factorKey e a)
        (SpecializedTriangular.diagonal_nonzero _ (factor_lower e a) (factor_unit e a)) P S hS := rfl
  exact (congrArg (fun ps => destination ps
    (TriangularStreams.tripleEncode (p, TriangularStreams.lexLayout x, s))) hp).trans
      (GlobalTriangular.destination_encoded sharedSpecialization f (factorKey e a)
        (SpecializedTriangular.diagonal_nonzero _ (factor_lower e a) (factor_unit e a))
        (factor_lower e a) P S hS p x s)

theorem factorProgram_destination (f : ℕ) (e : Edge) (a : Factor)
    (P S : ℕ) (hS : 0 < S) (p : Fin P) (x : Field f) (s : Fin S) :
    destination (factorProgram f e a P S hS)
        (TriangularStreams.tripleEncode (p, TriangularStreams.lexLayout (fieldVector f x), s)) =
      TriangularStreams.tripleEncode
        (p, TriangularStreams.lexLayout
          (fieldVector f ((factorMatrix f e a).mulVec x)), s) := by
  exact (factorProgram_destination_reduced f e a P S hS p (fieldVector f x) s).trans
    (congrArg (fun v => TriangularStreams.tripleEncode (p, TriangularStreams.lexLayout v, s))
      (fieldVector_mulVec f e a x))

/-- Casting an equal file length changes no address, primitive or cost. -/
def castProgram {V W : ℕ} (h : V = W) (ps : List (Pass V)) : List (Pass W) := h ▸ ps

@[simp] theorem castProgram_constant {V W : ℕ} (h : V = W) (ps : List (Pass V)) :
    totalConstant (castProgram h ps) = totalConstant ps := by subst W; rfl

def longVolume (f P G S : ℕ) : ℕ := P * ((radix ^ f) ^ Parameters.m *
  (G * ((radix ^ f) ^ Parameters.m * S)))

/-- High-coordinate passes see (G,D,S) as their suffix; low-coordinate
passes see (P,H,G) as their prefix. Their volumes are exactly equal. -/
def coordinateProgram (f : ℕ) (e : Edge) (a : Factor) (P G S : ℕ)
    (hG : 0 < G) (hS : 0 < S) : List (Pass (longVolume f P G S)) :=
  match a with
  | .left => factorProgram f e a P (G * ((radix ^ f) ^ Parameters.m * S))
      (Nat.mul_pos hG (Nat.mul_pos (pow_pos (pow_pos radix_prime.pos _) _) hS))
  | .leftInverse => factorProgram f e a P (G * ((radix ^ f) ^ Parameters.m * S))
      (Nat.mul_pos hG (Nat.mul_pos (pow_pos (pow_pos radix_prime.pos _) _) hS))
  | .right => castProgram (by unfold longVolume; ring)
      (factorProgram f e a (P * ((radix ^ f) ^ Parameters.m * G)) S hS)
  | .rightInverse => castProgram (by unfold longVolume; ring)
      (factorProgram f e a (P * ((radix ^ f) ^ Parameters.m * G)) S hS)

theorem coordinateProgram_constant (f : ℕ) (e : Edge) (a : Factor)
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) :
    totalConstant (coordinateProgram f e a P G S hG hS) ≤ factorConstant e a := by
  cases a <;> simp only [coordinateProgram, castProgram_constant] <;>
    exact factorProgram_constant _ _ _ _ _ _

def allCoordinateConstant : ℕ := ∑ e : Edge, ∑ a : Factor, factorConstant e a

/-- Each witness is for the array actually presented to that factor call.
This permits the recursive exchanges between the before/after calls;
the four factor programs are not incorrectly concatenated past a child. -/
theorem allCoordinate_executions {Value : Type*} [Inhabited Value]
    (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (inputs : Edge → Factor → Fin (longVolume f P G S) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ costs : Edge → Factor → ℕ,
      (∀ e a, Execution B hB (coordinateProgram f e a P G S hG hS) (inputs e a) (costs e a)) ∧
      (∑ e, ∑ a, costs e a) ≤ allCoordinateConstant * (longVolume f P G S / B + 1) := by
  have h (e : Edge) (a : Factor) := program_correct
    (coordinateProgram f e a P G S hG hS) (inputs e a) B hB
  choose costs he hc using h
  refine ⟨costs, he, ?_⟩
  calc
    (∑ e, ∑ a, costs e a) ≤ ∑ e, ∑ a,
        factorConstant e a * (longVolume f P G S / B + 1) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro a _
      exact (hc e a).trans (Nat.mul_le_mul_right _ (coordinateProgram_constant f e a P G S hG hS))
    _ = allCoordinateConstant * (longVolume f P G S / B + 1) := by
      simp only [allCoordinateConstant, Finset.sum_mul]


/-- Spectators produced by the actual selected-coordinate regrouping. -/
abbrev ChildPrefix (f P : ℕ) (c : Child) :=
  SingleCoordinate.ShortPrefix (Prefix := Fin P) (R := Scalar f) (childRow c)
abbrev ChildGap (f G : ℕ) (c : Child) :=
  SingleCoordinate.ShortGap (Gap := Fin G) (R := Scalar f) (childRow c) (childCol c)
abbrev ChildSuffix (f S : ℕ) (c : Child) :=
  SingleCoordinate.ShortSuffix (Suffix := Fin S) (R := Scalar f) (childCol c)

def childP (f P : ℕ) (c : Child) := Fintype.card (ChildPrefix f P c)
def childG (f G : ℕ) (c : Child) := Fintype.card (ChildGap f G c)
def childS (f S : ℕ) (c : Child) := Fintype.card (ChildSuffix f S c)

theorem field_card (f : ℕ) : Fintype.card (Field f) = (radix ^ f) ^ Parameters.m := by
  rw [long_field_card, ← pow_mul, Nat.mul_comm Parameters.m f]

theorem address_card {P H G S : Type}
    [Fintype P] [Fintype H] [Fintype G] [Fintype S] :
    Fintype.card (Address.FullAddress P H G S) =
      Fintype.card P * Fintype.card H * Fintype.card G * Fintype.card H * Fintype.card S := by
  rw [Fintype.card_congr fullAddressTuple]
  simp only [Fintype.card_prod]
  ring

theorem longAddress_card (f P G S : ℕ) :
    Fintype.card (LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) =
      longVolume f P G S := by
  rw [address_card, field_card]
  simp only [Fintype.card_fin, longVolume]
  ring

theorem childS_pos (f S : ℕ) (c : Child) (hS : 0 < S) : 0 < childS f S c := by
  letI : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  exact Fintype.card_pos

/-- No child's scan is charged per outer slice: regrouping preserves the
full stream volume, including every prefix, gap and suffix. -/
theorem child_volume (f P G S : ℕ) (c : Child) :
    (childP f P c * (radix ^ f * childG f G c)) * (radix ^ f * childS f S c) =
      longVolume f P G S := by
  have h := Fintype.card_congr
    (childRepack (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f c)
  rw [longAddress_card, address_card] at h
  simp only [short_field_card] at h
  change longVolume f P G S = childP f P c * radix ^ f * childG f G c *
    radix ^ f * childS f S c at h
  rw [h]
  ring

/-- The two actual scalar programs around a child, transported only across
an equality of total file lengths. -/
def scalarBefore (f P G S : ℕ) (c : Child) : List (Pass (longVolume f P G S)) :=
  castProgram (child_volume f P G S c)
    (ScalarCoordinateProgram.before (P := childP f P c) (Q := radix ^ f)
      (G := childG f G c) (S := childS f S c))

def scalarAfter (f P G S : ℕ) (c : Child) (hS : 0 < S) : List (Pass (longVolume f P G S)) :=
  castProgram (child_volume f P G S c)
    (ScalarCoordinateProgram.after (P := childP f P c) (Q := radix ^ f)
      (G := childG f G c) (childS_pos f S c hS))

@[simp] theorem scalarBefore_constant (f P G S : ℕ) (c : Child) :
    totalConstant (scalarBefore f P G S c) = 10 := by
  rw [scalarBefore, castProgram_constant, ScalarCoordinateProgram.before_constant]

@[simp] theorem scalarAfter_constant (f P G S : ℕ) (c : Child) (hS : 0 < S) :
    totalConstant (scalarAfter f P G S c hS) = 20 := by
  rw [scalarAfter, castProgram_constant, ScalarCoordinateProgram.after_constant]

/-- The inputs may be the different arrays before and after the recursive
child. Every scalar phase is charged for its actual canonical disk execution. -/
theorem allScalar_executions {Value : Type*} [Inhabited Value]
    (f P G S : ℕ) (hS : 0 < S)
    (beforeInputs afterInputs : Child → Fin (longVolume f P G S) → Value)
    (B : ℕ) (hB : 0 < B) :
    ∃ beforeCost afterCost : Child → ℕ,
      (∀ c, Execution B hB (scalarBefore f P G S c) (beforeInputs c) (beforeCost c)) ∧
      (∀ c, Execution B hB (scalarAfter f P G S c hS) (afterInputs c) (afterCost c)) ∧
      (∑ c : Child, (beforeCost c + afterCost c)) ≤ 30 * Parameters.S * (longVolume f P G S / B + 1) := by
  have hb (c : Child) := program_correct (scalarBefore f P G S c) (beforeInputs c) B hB
  have ha (c : Child) := program_correct (scalarAfter f P G S c hS) (afterInputs c) B hB
  choose beforeCost heB hcB using hb
  choose afterCost heA hcA using ha
  refine ⟨beforeCost, afterCost, heB, heA, ?_⟩
  calc
    (∑ c : Child, (beforeCost c + afterCost c)) ≤ ∑ _c : Child, 30 * (longVolume f P G S / B + 1) := by
      apply Finset.sum_le_sum
      intro c _
      have hb' := hcB c
      have ha' := hcA c
      rw [scalarBefore_constant] at hb'
      rw [scalarAfter_constant] at ha'
      omega
    _ = 30 * Parameters.S * (longVolume f P G S / B + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, child_count, smul_eq_mul]
      ring

/-- Uniform fixed constant for all nonrecursive matrix/scalar address work.
It depends only on the finite rational network construction. -/
def addressLocalConstant : ℕ := allCoordinateConstant + 30 * Parameters.S

/-- Address-work evidence contains the actual execution of every primitive
call and the sum of exactly those returned costs. Payload inputs may be the
arrays occurring at arbitrary points of the enclosing coded interpreter. -/
def AddressWork {Value : Type*} [Inhabited Value]
    (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (factorInputs : Edge → Factor → Fin (longVolume f P G S) → Value)
    (beforeInputs afterInputs : Child → Fin (longVolume f P G S) → Value)
    (B : ℕ) (hB : 0 < B) (cost : ℕ) : Prop :=
  ∃ factors : Edge → Factor → ℕ, ∃ before after : Child → ℕ,
    (∀ e a, Execution B hB (coordinateProgram f e a P G S hG hS) (factorInputs e a) (factors e a)) ∧
    (∀ c, Execution B hB (scalarBefore f P G S c) (beforeInputs c) (before c)) ∧
    (∀ c, Execution B hB (scalarAfter f P G S c hS) (afterInputs c) (after c)) ∧
    cost = (∑ e, ∑ a, factors e a) + (∑ c : Child, (before c + after c))

theorem addressWork_exists {Value : Type*} [Inhabited Value]
    (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (factorInputs : Edge → Factor → Fin (longVolume f P G S) → Value)
    (beforeInputs afterInputs : Child → Fin (longVolume f P G S) → Value)
    (B : ℕ) (hB : 0 < B) :
    ∃ cost, AddressWork f P G S hG hS factorInputs beforeInputs afterInputs B hB cost ∧
      cost ≤ addressLocalConstant * (longVolume f P G S / B + 1) := by
  obtain ⟨factors, heF, hcF⟩ := allCoordinate_executions f P G S hG hS factorInputs B hB
  obtain ⟨before, after, heB, heA, hcS⟩ :=
    allScalar_executions f P G S hS beforeInputs afterInputs B hB
  refine ⟨(∑ e, ∑ a, factors e a) + (∑ c : Child, (before c + after c)),
    ⟨factors, before, after, heF, heB, heA, rfl⟩, ?_⟩
  rw [addressLocalConstant, Nat.add_mul]
  exact Nat.add_le_add hcF hcS

theorem absorb_startup (V B C cost : ℕ) (hV : B ≤ V)
    (hc : cost ≤ C * (V / B + 1)) : cost * B ≤ 2 * C * V := by
  have hd := Nat.div_mul_le_self V B
  calc
    cost * B ≤ (C * (V / B + 1)) * B := Nat.mul_le_mul_right B hc
    _ = C * ((V / B) * B + B) := by ring
    _ ≤ C * (V + V) := Nat.mul_le_mul_left C (Nat.add_le_add hd hV)
    _ = 2 * C * V := by ring


/-- Exact interface for the pruned recursive cost proof. Startup is absorbed
only when the current per-role stream contains at least one physical block. -/
theorem addressWork_outside_cutoff {Value : Type*} [Inhabited Value]
    (f P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (factorInputs : Edge → Factor → Fin (longVolume f P G S) → Value)
    (beforeInputs afterInputs : Child → Fin (longVolume f P G S) → Value)
    (B : ℕ) (hB : 0 < B) (hV : B ≤ longVolume f P G S) :
    ∃ cost, AddressWork f P G S hG hS factorInputs beforeInputs afterInputs B hB cost ∧
      cost * B ≤ 2 * addressLocalConstant * longVolume f P G S := by
  obtain ⟨cost, he, hc⟩ := addressWork_exists f P G S hG hS factorInputs beforeInputs afterInputs B hB
  exact ⟨cost, he, absorb_startup _ _ _ _ hV hc⟩


end
end CSL.RecursiveExchangeCost


