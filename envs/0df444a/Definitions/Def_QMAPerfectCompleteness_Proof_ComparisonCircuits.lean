-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
-- name    : QMAPerfectCompleteness_Proof_ComparisonCircuits
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:51:50.97523+00:00
-- url     : https://prove2.me/theorems/183b053e-169e-4ae5-9472-d17d2ba64408
-- title:
--   Binary comparison with fixed thresholds
-- statement:
--   Defines reversible comparisons of a binary register with a fixed integer by first-differing-bit tests. The accompanying bit-value and prefix identities connect the physical controls with the intended integer inequality.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ComparisonCircuits.lean, retained declaration span lines 9–317.

/- Generated from Solutions.ComparisonCircuits by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Constant comparisons by disjoint first-differing-bit tests. -/

open Matrix
namespace QMAPerfectCompleteness.Main.ComparisonCircuits
open ReversibleGadgets ControlCircuits EqualityCircuits

/-- Numeric value of an initial most-significant-first prefix. -/
def prefixValue {r : ℕ} (x : Fin r → Bool) : (t : ℕ) → t ≤ r → ℕ
  | 0, _ => 0
  | t+1, ht => 2 * prefixValue x t (by omega) + if x ⟨t, by omega⟩ then 1 else 0

theorem prefixValue_eq_iff {r : ℕ} (x p : Fin r → Bool) (t : ℕ) (ht : t ≤ r) :
    prefixValue x t ht = prefixValue p t ht ↔ ∀ j : Fin r, (j : ℕ) < t → x j = p j := by
  induction t with
  | zero => simp [prefixValue]
  | succ t ih =>
    let u : Fin r := ⟨t, by omega⟩
    have hdigits : (2 * prefixValue x t (by omega) + (if x u then 1 else 0) =
        2 * prefixValue p t (by omega) + (if p u then 1 else 0)) ↔
        prefixValue x t (by omega) = prefixValue p t (by omega) ∧ x u = p u := by
      cases hx : x u <;> cases hp : p u <;> simp_all <;> omega
    change (2 * prefixValue x t (by omega) + (if x u then 1 else 0) =
      2 * prefixValue p t (by omega) + (if p u then 1 else 0)) ↔ _
    rw [hdigits, ih (by omega)]
    constructor
    · rintro ⟨hp, hn⟩ j hj
      by_cases hlt : (j : ℕ) < t
      · exact hp j hlt
      · have heq : j = u := by apply Fin.ext; change j.val = t; omega
        simpa only [heq] using hn
    · intro h
      exact ⟨fun j hj => h j (by omega), h u (by dsimp [u]; omega)⟩

/-- Comparison of two equal-length binary prefixes evolves by the unique new differing bit. -/
theorem binary_step_compare (a b : ℕ) (u v : Bool) :
    decide (2*a + (if u then 1 else 0) < 2*b + (if v then 1 else 0)) =
      xor (decide (a < b)) (decide (a = b ∧ u = false ∧ v = true)) := by
  apply Bool.eq_iff_iff.mpr
  cases u <;> cases v <;> simp [Bool.coe_xor_iff] <;> omega

/-- Little-endian integer represented by a fixed-width bit string. -/
def littleValue {r : ℕ} (x : Fin r → Bool) : ℕ := ∑ j, if x j then 2 ^ (j : ℕ) else 0

/-- A fold over high bits has the usual binary positional value. -/
theorem prefixValue_weighted {r : ℕ} (x : Fin r → Bool) (t : ℕ) (ht : t ≤ r) :
    prefixValue x t ht = ∑ j : Fin t,
      if x ⟨j, Nat.lt_of_lt_of_le j.isLt ht⟩ then 2 ^ (t-1-(j : ℕ)) else 0 := by
  induction t with
  | zero => simp [prefixValue]
  | succ t ih =>
    rw [prefixValue, ih (by omega), Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : t - (j : ℕ) = (t-1-(j : ℕ)) + 1 := by omega
    cases hx : x ⟨j, Nat.lt_of_lt_of_le j.isLt (by omega : t ≤ r)⟩ <;>
      simp [hx, he, pow_succ, Nat.mul_comm]

/-- Reading the wires from high bit to low bit gives their little-endian integer value. -/
theorem prefixValue_reverse {r : ℕ} (x : Fin r → Bool) :
    prefixValue (fun j => x j.rev) r le_rfl = littleValue x := by
  rw [prefixValue_weighted]
  change (∑ j : Fin r, if x j.rev then 2 ^ (r-1-(j : ℕ)) else 0) = _
  have hrev : ∀ j : Fin r, r-1-(j : ℕ) = (j.rev : ℕ) := by intro j; simp only [Fin.val_rev]; omega
  simp_rw [hrev]
  exact (Equiv.sum_comp (Fin.revPerm) (fun j : Fin r => if x j then 2 ^ (j : ℕ) else 0))

variable {r n : ℕ} (L : AndLayout r n)

/-- Restrict an AND layout to an initial segment, reusing the first scratch flags. -/
def prefixLayout (t : ℕ) (ht : t ≤ r) : AndLayout t n where
  controls := ⟨fun j => L.controls ⟨j, Nat.lt_of_lt_of_le j.isLt ht⟩,
    fun i j h => Fin.ext (congrArg (fun a : Fin r => a.val) (L.controls.injective h))⟩
  flags := ⟨fun j => L.flags ⟨j, by have := j.isLt; omega⟩,
    fun i j h => Fin.ext (congrArg (fun a : Fin (r+1) => a.val) (L.flags.injective h))⟩
  disjoint i j := L.disjoint _ _

/-- At the new bit, a smaller word has zero; every preceding higher bit equals the threshold. -/
def stagePattern (p : Fin r → Bool) (t : ℕ) (ht : t < r) (j : Fin (t+1)) : Bool :=
  if (j : ℕ) < t then p ⟨j, by omega⟩ else false

def stageMatches (p : Fin r → Bool) (t : ℕ) (ht : t < r) (x : Basis n) : Prop :=
  (∀ j : Fin r, (j : ℕ) < t → x (L.controls j) = p j) ∧ x (L.controls ⟨t,ht⟩) = false

instance (p : Fin r → Bool) (t : ℕ) (ht : t < r) (x : Basis n) :
    Decidable (stageMatches L p t ht x) := inferInstanceAs (Decidable (_ ∧ _))

theorem stage_pattern_iff (p : Fin r → Bool) (t : ℕ) (ht : t < r) (x : Basis n) :
    (∀ j, x ((prefixLayout L (t+1) (by omega)).controls j) = stagePattern p t ht j) ↔
      stageMatches L p t ht x := by
  change (∀ j : Fin (t+1), x (L.controls ⟨j, by have := j.isLt; omega⟩) = stagePattern p t ht j) ↔ _
  constructor
  · intro h
    constructor
    · intro j hj
      have hj' : (j : ℕ) < t+1 := by omega
      simpa [prefixLayout, stagePattern, hj] using h ⟨j,hj'⟩
    · simpa [prefixLayout, stagePattern] using h (Fin.last t)
  · rintro ⟨hp,hn⟩ j
    by_cases hj : (j : ℕ) < t
    · simpa [prefixLayout, stagePattern, hj] using hp ⟨j, by omega⟩ hj
    · have heq : j = Fin.last t := by apply Fin.ext; have := j.isLt; change j.val = t; omega
      subst j
      simpa [prefixLayout, stagePattern] using hn

/-- A single first-differing-bit pattern circuit, enabled only for a one bit of the threshold. -/
noncomputable def stageGates (p : Fin r → Bool) (target : Fin n) (hf : ∀ j, target ≠ L.flags j)
    (t : ℕ) (ht : t < r) : List (Instr gatesG2 n) :=
  if p ⟨t,ht⟩ then patternControlledX (prefixLayout L (t+1) (by omega))
    (stagePattern p t ht) target (fun j => hf _) else []

def stageBit (p : Fin r → Bool) (t : ℕ) (ht : t < r) (x : Basis n) : Bool :=
  if p ⟨t,ht⟩ then decide (stageMatches L p t ht x) else false

/-- The comparison flag is XOR of the disjoint first-differing-bit tests. -/
def comparePrefixBit (p : Fin r → Bool) (x : Basis n) : (t : ℕ) → t ≤ r → Bool
  | 0, _ => false
  | t+1, ht => xor (comparePrefixBit p x t (by omega)) (stageBit L p t (by omega) x)

noncomputable def comparePrefixGates (p : Fin r → Bool) (target : Fin n)
    (hf : ∀ j, target ≠ L.flags j) : (t : ℕ) → t ≤ r → List (Instr gatesG2 n)
  | 0, _ => []
  | t+1, ht => comparePrefixGates p target hf t (by omega) ++ stageGates L p target hf t (by omega)

theorem stageBit_numeric (p : Fin r → Bool) (t : ℕ) (ht : t < r) (x : Basis n) :
    stageBit L p t ht x = decide
      (prefixValue (fun j => x (L.controls j)) t (by omega) = prefixValue p t (by omega) ∧
        x (L.controls ⟨t,ht⟩) = false ∧ p ⟨t,ht⟩ = true) := by
  apply Bool.eq_iff_iff.mpr
  cases hp : p ⟨t,ht⟩ <;> simp [stageBit, stageMatches, hp, prefixValue_eq_iff]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- The XOR is a genuine numeric comparison; simultaneous terms cannot cancel because the
new pattern requires equality of every earlier higher bit. -/
theorem comparePrefixBit_correct (p : Fin r → Bool) (x : Basis n) (t : ℕ) (ht : t ≤ r) :
    comparePrefixBit L p x t ht =
      decide (prefixValue (fun j => x (L.controls j)) t ht < prefixValue p t ht) := by
  induction t with
  | zero => simp [comparePrefixBit, prefixValue]
  | succ t ih =>
    rw [comparePrefixBit, ih (by omega), stageBit_numeric]
    exact (binary_step_compare _ _ _ _).symm

theorem stageBit_update_other (p : Fin r → Bool) (t : ℕ) (ht : t < r)
    (x : Basis n) (w : Fin n) (b : Bool) (hw : ∀ j, w ≠ L.controls j) :
    stageBit L p t ht (Function.update x w b) = stageBit L p t ht x := by
  have hread : ∀ j, Function.update x w b (L.controls j) = x (L.controls j) :=
    fun j => Function.update_of_ne (hw j).symm _ _
  apply Bool.eq_iff_iff.mpr
  simp only [stageBit, stageMatches, hread]
  rfl



theorem stageGates_matrix (p : Fin r → Bool) (target : Fin n)
    (hc : ∀ j, target ≠ L.controls j) (hf : ∀ j, target ≠ L.flags j)
    (t : ℕ) (ht : t < r) (y x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (stageGates L p target hf t ht) y x =
      if y = Function.update x target (xor (x target) (stageBit L p t ht x)) then 1 else 0 := by
  cases hp : p ⟨t,ht⟩
  · simp only [stageGates, hp, Bool.false_eq_true, if_false, circuitMatrix,
      stageBit, Bool.xor_false, Function.update_eq_self]
    rfl
  · have h := patternControlledX_matrix (prefixLayout L (t+1) (by omega))
      (stagePattern p t ht) target (fun j => hc _) (fun j => hf _) y x (fun j => hclean _)
    simpa only [stageGates, stageBit, hp, if_true, stage_pattern_iff] using h



theorem comparePrefixGates_matrix (p : Fin r → Bool) (target : Fin n)
    (hc : ∀ j, target ≠ L.controls j) (hf : ∀ j, target ≠ L.flags j)
    (t : ℕ) (ht : t ≤ r) (y x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (comparePrefixGates L p target hf t ht) y x =
      if y = Function.update x target (xor (x target) (comparePrefixBit L p x t ht)) then 1 else 0 := by
  induction t generalizing y x with
  | zero =>
    simp only [comparePrefixGates, circuitMatrix, comparePrefixBit, Bool.xor_false, Function.update_eq_self]
    rfl
  | succ t ih =>
    rw [comparePrefixGates, BlockProof.circuitMatrix_append, Matrix.mul_apply]
    simp_rw [ih (by omega) _ x hclean]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hcn : ∀ j, (Function.update x target (xor (x target) (comparePrefixBit L p x t (by omega))))
        (L.flags j) = false := by
      intro j
      rw [Function.update_of_ne (hf j).symm]
      exact hclean j
    rw [stageGates_matrix L p target hc hf t (by omega) y _ hcn,
      stageBit_update_other L p t (by omega) x target _ hc]
    simp only [Function.update_self, Function.update_idem, comparePrefixBit, Bool.xor_assoc]
    rfl

/-- Reverse only the control order: physical bit i remains the little-endian i-th bit. -/
def reverseLayout : AndLayout r n where
  controls := ⟨fun j => L.controls j.rev, by
    intro i j h
    have he := L.controls.injective h
    exact Fin.rev_injective he⟩
  flags := L.flags
  disjoint i j := L.disjoint i.rev j

/-- A literal polynomial-size circuit comparing a little-endian word to a fixed bit pattern. -/
noncomputable def compareGates (p : Fin r → Bool) (target : Fin n)
    (hf : ∀ j, target ≠ L.flags j) : List (Instr gatesG2 n) :=
  comparePrefixGates (reverseLayout L) (fun j => p j.rev) target hf r le_rfl



/-- Exact numeric less-than comparison. The target is XORed with [word<threshold], and every
other bit (including all r+1 clean scratch flags) is restored. -/
theorem compareGates_matrix (p : Fin r → Bool) (target : Fin n)
    (hc : ∀ j, target ≠ L.controls j) (hf : ∀ j, target ≠ L.flags j)
    (y x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (compareGates L p target hf) y x =
      if y = Function.update x target (xor (x target)
        (decide (littleValue (fun j => x (L.controls j)) < littleValue p))) then 1 else 0 := by
  have hmat := comparePrefixGates_matrix (reverseLayout L) (fun j => p j.rev) target
    (fun j => hc j.rev) (fun j => hf j) r le_rfl y x (fun j => hclean j)
  have hbit : comparePrefixBit (reverseLayout L) (fun j => p j.rev) x r le_rfl =
      decide (littleValue (fun j => x (L.controls j)) < littleValue p) := by
    rw [comparePrefixBit_correct]
    change decide (prefixValue (fun j => x (L.controls j.rev)) r le_rfl <
      prefixValue (fun j => p j.rev) r le_rfl) = _
    rw [prefixValue_reverse (fun j => x (L.controls j)), prefixValue_reverse p]
  simpa only [compareGates, hbit] using hmat

/-- Binary positional values of fixed-width words lie in their representable range. -/
theorem prefixValue_lt_two_pow {k : ℕ} (x : Fin k → Bool) (t : ℕ) (ht : t ≤ k) :
    prefixValue x t ht < 2 ^ t := by
  induction t with
  | zero => simp [prefixValue]
  | succ t ih =>
    have hi := ih (by omega)
    rw [prefixValue, pow_succ]
    cases hx : x ⟨t, by omega⟩ <;> simp [hx] <;> omega

theorem littleValue_lt_two_pow {k : ℕ} (x : Fin k → Bool) : littleValue x < 2 ^ k := by
  rw [← prefixValue_reverse x]
  exact prefixValue_lt_two_pow _ _ _

/-- Natural-number threshold bits encode that threshold modulo the word size. -/
theorem littleValue_testBit (a k : ℕ) : littleValue (fun j : Fin k => a.testBit j) = a % 2 ^ k := by
  induction k with
  | zero =>
    change 0 = a % 1
    exact (Nat.mod_one a).symm
  | succ k ih =>
    simp only [littleValue] at ih ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.mod_pow_succ]
    congr 1
    have hm : (a / 2^k) % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases hbit : (a / 2^k) % 2 = 1
    · simp [Nat.testBit_eq_decide_div_mod_eq, hbit]
    · have hzero : (a / 2^k) % 2 = 0 := by omega
      simp [Nat.testBit_eq_decide_div_mod_eq, hzero]

/-- Compare to an arbitrary natural threshold; thresholds beyond the word range are always true. -/
noncomputable def compareNatGates (a : ℕ) (target : Fin n) (hf : ∀ j, target ≠ L.flags j) :
    List (Instr gatesG2 n) :=
  if a < 2 ^ r then compareGates L (fun j => a.testBit j) target hf else [xAt target]



theorem compareNatGates_matrix (a : ℕ) (target : Fin n)
    (hc : ∀ j, target ≠ L.controls j) (hf : ∀ j, target ≠ L.flags j)
    (y x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (compareNatGates L a target hf) y x =
      if y = Function.update x target (xor (x target)
        (decide (littleValue (fun j => x (L.controls j)) < a))) then 1 else 0 := by
  unfold compareNatGates
  split
  · rename_i ha
    rw [compareGates_matrix L _ target hc hf y x hclean, littleValue_testBit,
      Nat.mod_eq_of_lt ha]
  · rename_i ha
    have hlt : littleValue (fun j => x (L.controls j)) < a :=
      (littleValue_lt_two_pow _).trans_le (Nat.le_of_not_gt ha)
    simp only [hlt, decide_true, Bool.xor_true, circuitMatrix, Matrix.one_mul, xAt_matrix,
      classicalMatrix, Matrix.of_apply, xAction]
    rfl

/-- The comparator uses the identical little-endian wire-value convention as the block compiler. -/
theorem compareNatGates_matrix_bitsValue (a : ℕ) (target : Fin n)
    (hc : ∀ j, target ≠ L.controls j) (hf : ∀ j, target ≠ L.flags j)
    (y x : Basis n) (hclean : ∀ j, x (L.flags j) = false) :
    circuitMatrix (compareNatGates L a target hf) y x =
      if y = Function.update x target (xor (x target)
        (decide (BlockCircuit.bitsValue x L.controls < a))) then 1 else 0 :=
  compareNatGates_matrix L a target hc hf y x hclean

end QMAPerfectCompleteness.Main.ComparisonCircuits


