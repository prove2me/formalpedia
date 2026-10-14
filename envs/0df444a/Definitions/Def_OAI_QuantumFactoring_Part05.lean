-- Prove2me | Definitions.Def_OAI_QuantumFactoring_Part05
-- name    : OAI_QuantumFactoring_Part05
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T07:05:47.875616+00:00
-- url     : https://prove2.me/theorems/0da1e43a-df96-4d0c-ba5e-0b3ddd610d24
-- title:
--   Exact quantum factoring, part 5 of 38 (port of OpenAI's formalization)
-- statement:
--   Part 5 of 38 of a port of OpenAI's Lean formalization of the manuscript *Exact quantum factoring over a fixed finite gate set* (OpenAI, September 25, 2026). This part contains the modules `OrderTrialFurther2`, `Exactness`, `SuperpositionGates`, `PhasePreparation`, `PhasePreparationConnection`, `BitResidue`, `HadamardAction`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/QuantumFactoring`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `ExactQuantumFactoring`, which is identical to upstream `Basic.lean`. This part also makes small compatibility edits for Lean 4.33.1 / Mathlib 0df444a: in OrderTrialFurther2.lean, finish `quarterPairs_card` with `decide` after `norm_num`.
--
--   The development is split into 38 parts only so that each compiles within the platform's time limit. Together the parts supply the circuit family `PhysicalTree.finalCircuit` and its specification, used to prove `OAI.ExactQuantumFactoring.zero_amplitude_core`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/QuantumFactoring: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/OrderTrialFurther2.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/Exactness.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/SuperpositionGates.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhasePreparation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/PhasePreparationConnection.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/BitResidue.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/QuantumFactoring/HadamardAction.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf

/-
Exact quantum factoring development (port of OpenAI's formalization), part 5 of 38.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/QuantumFactoring/: OrderTrialFurther2.lean, Exactness.lean, SuperpositionGates.lean, PhasePreparation.lean, PhasePreparationConnection.lean, BitResidue.lean, HadamardAction.lean
These files formalize the manuscript "Exact quantum factoring over a fixed finite gate set"
(OpenAI, September 25, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Basic.lean) come from the platform definition `ExactQuantumFactoring`, to which upstream
Basic.lean is identical; the final assembly (Main.lean) is omitted; compatibility edits for the platform Lean/Mathlib versions: in OrderTrialFurther2.lean, finish `quarterPairs_card` with `decide` after `norm_num`.
-/
import Mathlib
import Definitions.Def_OAI_QuantumFactoring_Part04

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/OrderTrialFurther2.lean =====
namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma largeQ (B : ℕ) (hB : 2 ≤ B) : 65*B ≤ B^16 := by
  have h : 65 ≤ B^15 := by
    calc
      65 ≤ (2:ℕ)^15 := by norm_num
      _ ≤ B^15 := Nat.pow_le_pow_left hB 15
  calc
    _ ≤ B^15*B := Nat.mul_le_mul_right B h
    _ = B^16 := (pow_succ B 15).symm

/-- The literal majorant-sum estimate at the standing Q=B^16. -/
lemma majorantSum_bounds {B d : ℕ} (hB : 2 ≤ B) (hd : 0 < d) (hdB : d < B) (j : ℕ) :
    1/(128*(d:ℝ)) ≤ (majorantSum (B^16) B d j:ℝ) ∧
      (majorantSum (B^16) B d j:ℝ) ≤ 2 := by
  have hQ : 0 < B^16 := pow_pos (by omega) _
  refine ⟨majorantSum_lower hQ hB hd hdB.le j, (majorantSum_upper hQ hB hd hdB.le j).trans ?_⟩
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hQ' : (0:ℝ) < (B^16:ℕ) := Nat.cast_pos.mpr hQ
  have h65 : (65:ℝ)*d ≤ (B^16:ℕ) := by
    exact_mod_cast (Nat.mul_le_mul_left 65 hdB.le).trans (largeQ B hB)
  have h₁ : 1/(2*(d:ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*d)).mpr
    linarith
  have h₂ : 65*(d:ℝ)/(2*(B^16:ℕ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(B^16:ℕ))).mpr
    linarith
  linarith

/-- Integer numerator retained by upward rounding at an integer argument. -/
noncomputable def roundedNumerator (D : ℕ) (p : ℚ[X]) (u : ℕ) : ℤ :=
  ∑ q ∈ Finset.range 5, ⌈(D:ℚ)*p.coeff q⌉*(u:ℤ)^q

lemma roundedValue_numerator (D : ℕ) (p : ℚ[X]) (u : ℕ) :
    roundedValue D p u = (roundedNumerator D p u:ℚ)/D := by
  simp only [roundedValue, roundedNumerator, roundCoeff, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  ring

noncomputable def majorantNumerator (Q B d j u : ℕ) : ℤ :=
  roundedNumerator (Q*B^8) (selectedMass d (binErrorRat Q d j) u) u+64*(B:ℤ)^8

lemma majorant_numerator {Q B : ℕ} (hQ : 0 < Q) (hB : 0 < B) (d j u : ℕ) :
    majorant Q B d j u = (majorantNumerator Q B d j u:ℚ)/(Q*B^8) := by
  simp only [majorant, majorantNumerator, roundedValue_numerator, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow]
  have hQ' : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hB' : (B:ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

lemma majorantSum_numerator {Q B : ℕ} (hQ : 0 < Q) (hB : 0 < B) (d j : ℕ) :
    majorantSum Q B d j =
      ((∑ u ∈ Finset.range d, majorantNumerator Q B d j u : ℤ):ℚ)/(2*(Q*B^8)) := by
  simp only [majorantSum, majorant_numerator hQ hB, Int.cast_sum, ← Finset.sum_div]
  ring

/-- Dyadic means an integer over a nonnegative integral power of two. -/
def IsDyadic (x : ℚ) : Prop := ∃ k : ℕ, ∃ z : ℤ, x = (z:ℚ)/2^k

lemma majorant_dyadic (n d j u : ℕ) :
    IsDyadic (majorant ((2^n)^16) (2^n) d j u) := by
  refine ⟨n*24, majorantNumerator ((2^n)^16) (2^n) d j u, ?_⟩
  rw [majorant_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_add, ← pow_mul]

lemma majorantSum_dyadic (n d j : ℕ) :
    IsDyadic (majorantSum ((2^n)^16) (2^n) d j) := by
  refine ⟨n*24+1, ∑ u ∈ Finset.range d, majorantNumerator ((2^n)^16) (2^n) d j u, ?_⟩
  rw [majorantSum_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_add, ← pow_mul, pow_succ]
  ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Five closed power-sum formulas, not an enumeration up to the endpoint. -/
def powerSumValue (q : ℕ) (M : ℚ) : ℚ :=
  match q with
  | 0 => M
  | 1 => M*(M-1)/2
  | 2 => M*(M-1)*(2*M-1)/6
  | 3 => (M*(M-1)/2)^2
  | 4 => M*(M-1)*(2*M-1)*(3*M^2-3*M-1)/30
  | _ => 0

lemma powerSumValue_correct (q : ℕ) (hq : q ≤ 4) (M : ℕ) :
    powerSumValue q M = ∑ u ∈ Finset.range M, (u:ℚ)^q := by
  induction M with
  | zero => interval_cases q <;> norm_num [powerSumValue]
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    interval_cases q <;> simp only [powerSumValue] <;> ring

lemma powerSumValue_sub {lo hi : ℕ} (h : lo ≤ hi) {q : ℕ} (hq : q ≤ 4) :
    powerSumValue q hi-powerSumValue q lo = ∑ u ∈ Finset.Ico lo hi, (u:ℚ)^q := by
  rw [Finset.sum_Ico_eq_sub _ h, powerSumValue_correct q hq, powerSumValue_correct q hq]

/-- Constant-length arithmetic formula for summing a degree-four expression. -/
def fiveTermSum (a : ℕ → ℚ) (lo hi : ℕ) : ℚ :=
  if lo ≤ hi then ∑ q ∈ Finset.range 5, a q*(powerSumValue q hi-powerSumValue q lo) else 0

lemma fiveTermSum_correct (a : ℕ → ℚ) (lo hi : ℕ) :
    fiveTermSum a lo hi = ∑ u ∈ Finset.Ico lo hi, ∑ q ∈ Finset.range 5, a q*(u:ℚ)^q := by
  unfold fiveTermSum
  split_ifs with h
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [powerSumValue_sub h (by simp only [Finset.mem_range] at hq; omega), Finset.mul_sum]
  · simp [Finset.Ico_eq_empty (by omega : ¬ lo < hi)]

/-- Clipped natural endpoints for the intersection of two rational intervals. -/
def intervalLo (a c : ℚ) : ℕ := max ⌈a⌉.toNat ⌈c⌉.toNat

def intervalHi (d : ℕ) (b e : ℚ) : ℕ := min d (min ⌈b⌉.toNat ⌈e⌉.toNat)

lemma interval_mem_iff (d u : ℕ) (a b c e : ℚ) :
    u ∈ Finset.Ico (intervalLo a c) (intervalHi d b e) ↔
      u < d ∧ a ≤ (u:ℚ) ∧ (u:ℚ) < b ∧ c ≤ (u:ℚ) ∧ (u:ℚ) < e := by
  simp only [Finset.mem_Ico, intervalLo, intervalHi, max_le_iff, lt_min_iff,
    Int.toNat_le, Int.lt_toNat, Int.ceil_le, Int.lt_ceil, Int.cast_natCast]
  tauto

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

lemma quarterIndex_eq (x : ℚ) (q : ℤ) :
    quarterIndex x=q ↔ (q:ℚ)/4 ≤ x ∧ x < ((q:ℚ)+1)/4 := by
  unfold quarterIndex
  rw [Int.floor_eq_iff]
  constructor <;> rintro ⟨hl,hu⟩ <;> constructor <;> linarith

lemma shiftedQuarter_eq {d : ℕ} (hd : 0 < d) (u : ℕ) (η : ℚ) (q : ℤ) :
    quarterIndex ((u:ℚ)/d+η)=q ↔
      (d:ℚ)*((q:ℚ)/4-η) ≤ u ∧ (u:ℚ) < d*(((q:ℚ)+1)/4-η) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  rw [quarterIndex_eq, ← sub_le_iff_le_add, ← lt_sub_iff_add_lt,
    le_div_iff₀ hd', div_lt_iff₀ hd']
  simp only [mul_comm]

/-- Exactly 32 possible quarter pairs. -/
noncomputable def quarterPairs : Finset (ℤ × ℤ) := (Finset.Ico 0 4) ×ˢ (Finset.Ico (-2) 6)

def pieceLabel (d : ℕ) (η : ℚ) (u : ℕ) : ℤ × ℤ :=
  (quarterIndex ((u:ℚ)/d), quarterIndex ((u:ℚ)/d+η))

lemma pieceLabel_mem {d : ℕ} (hd : 0 < d) {η : ℚ} (hη : |η| ≤ 1/2)
    {u : ℕ} (hu : u < d) : pieceLabel d η u ∈ quarterPairs := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hu₀ : (0:ℚ) ≤ (u:ℚ)/d := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hu₁ : (u:ℚ)/d < 1 := (div_lt_one hd').mpr (by exact_mod_cast hu)
  rcases abs_le.mp hη with ⟨hη₀,hη₁⟩
  simp only [pieceLabel, quarterPairs, Finset.mem_product, Finset.mem_Ico,
    quarterIndex, Int.le_floor, Int.floor_lt, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
  constructor <;> constructor <;> linarith

lemma quarterPairs_card : quarterPairs.card=32 := by norm_num [quarterPairs] <;> decide

def pieceLo (d : ℕ) (η : ℚ) (q : ℤ × ℤ) : ℕ :=
  intervalLo ((d:ℚ)*(q.1:ℚ)/4) ((d:ℚ)*((q.2:ℚ)/4-η))

def pieceHi (d : ℕ) (η : ℚ) (q : ℤ × ℤ) : ℕ :=
  intervalHi d ((d:ℚ)*((q.1:ℚ)+1)/4) ((d:ℚ)*(((q.2:ℚ)+1)/4-η))

lemma piece_fiber {d : ℕ} (hd : 0 < d) (η : ℚ) (q : ℤ × ℤ) :
    (Finset.range d).filter (fun u => pieceLabel d η u=q) =
      Finset.Ico (pieceLo d η q) (pieceHi d η q) := by
  ext u
  rw [Finset.mem_filter]
  simp only [Finset.mem_range, pieceLo, pieceHi, interval_mem_iff]
  rw [Prod.ext_iff]
  simp only [pieceLabel]
  have h₀ := shiftedQuarter_eq hd u 0 q.1
  simp only [add_zero, sub_zero] at h₀
  rw [h₀, shiftedQuarter_eq hd u η q.2]
  simp only [mul_div_assoc]
  tauto

/-- Each piece sum is computed with five closed power sums plus its length. -/
noncomputable def packedPieceSum (Q B d j : ℕ) (q : ℤ × ℤ) : ℚ :=
  let η := binErrorRat Q d j
  let lo := pieceLo d η q
  let hi := pieceHi d η q
  fiveTermSum (fun k => roundCoeff (Q*B^8) ((massPiece d η q.1 q.2).coeff k)) lo hi +
    ((hi-lo:ℕ):ℚ)*(64/(Q:ℚ))

lemma packedPieceSum_correct {Q B d : ℕ} (hd : 0 < d) (j : ℕ) (q : ℤ × ℤ) :
    packedPieceSum Q B d j q =
      ∑ u ∈ (Finset.range d).filter (fun u => pieceLabel d (binErrorRat Q d j) u=q),
        majorant Q B d j u := by
  let η := binErrorRat Q d j
  have hf := piece_fiber hd η q
  have he : ∀ u ∈ (Finset.range d).filter (fun u => pieceLabel d η u=q),
      majorant Q B d j u = roundedValue (Q*B^8) (massPiece d η q.1 q.2) u+64/(Q:ℚ) := by
    intro u hu
    have h := (Finset.mem_filter.mp hu).2
    have h₀ := congrArg Prod.fst h
    have h₁ := congrArg Prod.snd h
    simp only [pieceLabel] at h₀ h₁
    simp only [majorant, selectedMass, h₀, h₁, η]
  change packedPieceSum Q B d j q = ∑ u ∈ (Finset.range d).filter (fun u => pieceLabel d η u=q), _
  rw [Finset.sum_congr rfl he, hf, Finset.sum_add_distrib]
  simp only [packedPieceSum, fiveTermSum_correct, roundedValue, η,
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- Exact constant-piece evaluation: no traversal of the d residues. -/
noncomputable def packedMajorantSum (Q B d j : ℕ) : ℚ :=
  (∑ q ∈ quarterPairs, packedPieceSum Q B d j q)/2

lemma packedMajorantSum_correct {Q B d : ℕ} (hd : 0 < d) (j : ℕ) :
    packedMajorantSum Q B d j = majorantSum Q B d j := by
  unfold packedMajorantSum majorantSum
  congr 1
  simp only [packedPieceSum_correct hd]
  apply Finset.sum_fiberwise_of_maps_to
  intro u hu
  apply pieceLabel_mem hd
  · have h := binError_bound (Q:=Q) (j:=j) hd
    rw [← binErrorRat_cast] at h
    have h' : ((|binErrorRat Q d j|:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := by simpa using h
    exact Rat.cast_le.mp h'
  · exact Finset.mem_range.mp hu

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Exact prescribed per-numerator mass, with the manuscript's ceiling. -/
def prescribedMass (d : ℕ) : ℚ := 1/(2:ℚ)^(Nat.clog 2 d+10)

lemma prescribedMass_pos (d : ℕ) : 0 < prescribedMass d := by
  unfold prescribedMass
  positivity

lemma prescribedMass_upper {d : ℕ} (hd : 0 < d) :
    prescribedMass d ≤ 1/(1024*(d:ℚ)) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) d
  have h' : (d:ℚ) ≤ (2:ℚ)^(Nat.clog 2 d) := by exact_mod_cast h
  unfold prescribedMass
  rw [pow_add, show (2:ℚ)^10=1024 by norm_num]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

lemma prescribedMass_lower {d : ℕ} (hd : 0 < d) :
    1/(2048*(d:ℚ)) ≤ prescribedMass d := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hp : (2:ℕ)^(Nat.clog 2 d) ≤ 2*d := by
    by_cases h : d=1
    · simp [h]
    · have hd₁ : 1 < d := by omega
      have hc := Nat.clog_pos (by norm_num : 1 < 2) hd₁
      have hlt := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hd₁
      calc
        _ = 2^(Nat.clog 2 d-1)*2 := by rw [← pow_succ]; congr 1; omega
        _ ≤ d*2 := Nat.mul_le_mul_right 2 hlt.le
        _ = 2*d := by omega
  have hp' : (2:ℚ)^Nat.clog 2 d ≤ 2*d := by exact_mod_cast hp
  unfold prescribedMass
  rw [pow_add, show (2:ℚ)^10=1024 by norm_num]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith

/-- Downward dyadic ratio rounding, as in (mode-coefficient). -/
def modeCoeff (n : ℕ) (lam S : ℚ) : ℚ :=
  (⌊(2:ℚ)^(10*n)*(lam/S)⌋:ℤ)/(2:ℚ)^(10*n)

def modeRemainder (n : ℕ) (lam S : ℚ) : ℚ := lam-modeCoeff n lam S*S

lemma modeCoeff_basic (n : ℕ) {lam S : ℚ} (hlam : 0 ≤ lam) (hS : 0 < S) :
    0 ≤ modeCoeff n lam S ∧ modeCoeff n lam S ≤ lam/S ∧
      lam/S-modeCoeff n lam S ≤ 1/(2:ℚ)^(10*n) := by
  have hD : (0:ℚ) < 2^(10*n) := by positivity
  have hx : 0 ≤ (2:ℚ)^(10*n)*(lam/S) := mul_nonneg hD.le (div_nonneg hlam hS.le)
  have hf := Int.floor_le ((2:ℚ)^(10*n)*(lam/S))
  have hu := (Int.lt_floor_add_one ((2:ℚ)^(10*n)*(lam/S))).le
  have hfn : (0:ℚ) ≤ (⌊(2:ℚ)^(10*n)*(lam/S)⌋:ℤ) := by
    exact_mod_cast (Int.floor_nonneg.mpr hx)
  unfold modeCoeff
  refine ⟨div_nonneg hfn hD.le, ?_, ?_⟩
  · apply (div_le_iff₀ hD).mpr
    nlinarith
  · apply (mul_le_mul_iff_right₀ hD).mp
    rw [mul_sub, mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
    linarith

lemma modeRemainder_basic (n : ℕ) {lam S : ℚ} (hlam : 0 ≤ lam) (hS : 0 < S) :
    0 ≤ modeRemainder n lam S ∧ modeRemainder n lam S ≤ S/(2:ℚ)^(10*n) := by
  have h := modeCoeff_basic n hlam hS
  have he : modeRemainder n lam S = (lam/S-modeCoeff n lam S)*S := by
    unfold modeRemainder
    rw [sub_mul, div_mul_cancel₀ _ hS.ne']
  rw [he]
  refine ⟨mul_nonneg (sub_nonneg.mpr h.2.1) hS.le, ?_⟩
  calc
    _ ≤ (1/(2:ℚ)^(10*n))*S := mul_le_mul_of_nonneg_right h.2.2 hS.le
    _ = _ := by ring

lemma modeCoeff_bounds (n : ℕ) {d : ℕ} (hd : 0 < d) {S : ℚ}
    (hSl : 1/(128*(d:ℚ)) ≤ S) (hSu : S ≤ 2) :
    0 ≤ modeCoeff n (prescribedMass d) S ∧ modeCoeff n (prescribedMass d) S ≤ 1/8 ∧
      0 ≤ modeRemainder n (prescribedMass d) S ∧
      modeRemainder n (prescribedMass d) S ≤ 2/(2:ℚ)^(10*n) := by
  have hd' : (0:ℚ) < d := Nat.cast_pos.mpr hd
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hSl
  have hc := modeCoeff_basic n (prescribedMass_pos d).le hS
  have hr := modeRemainder_basic n (prescribedMass_pos d).le hS
  refine ⟨hc.1, hc.2.1.trans ?_, hr.1, hr.2.trans ?_⟩
  · apply (div_le_iff₀ hS).mpr
    have hl := prescribedMass_upper hd
    have he : 1/(1024*(d:ℚ)) = (1/8)*(1/(128*(d:ℚ))) := by ring
    rw [he] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hSl (by norm_num))
  · exact div_le_div_of_nonneg_right hSu (by positivity)

lemma sum_residue_permutation {α : Type*} [AddCommMonoid α] {d j : ℕ}
    (hd : 0 < d) (hj : Nat.Coprime j d) (f : ℕ → α) :
    (∑ t ∈ Finset.range d, f ((j*t)%d)) = ∑ u ∈ Finset.range d, f u := by
  let g : Fin d → Fin d := fun t => ⟨(j*t.val)%d, Nat.mod_lt _ hd⟩
  have hi : Function.Injective g := by
    intro a b hab
    apply Fin.ext
    have he : Nat.ModEq d (j*a.val) (j*b.val) := congrArg Fin.val hab
    have h := he.cancel_left_of_coprime hj.symm
    change a.val % d = b.val % d at h
    simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h
  have hb : Function.Bijective g := ⟨hi, Finite.surjective_of_injective hi⟩
  have h := (Equiv.ofBijective g hb).sum_comp (fun u : Fin d => f u.val)
  change (∑ t : Fin d, f ((j*t.val)%d)) = ∑ u : Fin d, f u.val at h
  rw [Fin.sum_univ_eq_sum_range (fun t => f ((j*t)%d)) d,
    Fin.sum_univ_eq_sum_range f d] at h
  exact h

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

lemma IsDyadic.intCast (z : ℤ) : IsDyadic (z:ℚ) := ⟨0,z,by simp⟩

lemma IsDyadic.add {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x+y) := by
  obtain ⟨k,a,rfl⟩ := hx
  obtain ⟨l,b,rfl⟩ := hy
  refine ⟨k+l,a*2^l+b*2^k,?_⟩
  push_cast
  rw [pow_add]
  field_simp

lemma IsDyadic.neg {x : ℚ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨k,a,rfl⟩ := hx
  exact ⟨k,-a,by push_cast; ring⟩

lemma IsDyadic.sub {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x-y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

lemma IsDyadic.mul {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x*y) := by
  obtain ⟨k,a,rfl⟩ := hx
  obtain ⟨l,b,rfl⟩ := hy
  refine ⟨k+l,a*b,?_⟩
  push_cast
  rw [pow_add]
  ring

lemma prescribedMass_dyadic (d : ℕ) : IsDyadic (prescribedMass d) :=
  ⟨Nat.clog 2 d+10,1,by simp [prescribedMass]⟩

lemma modeCoeff_dyadic (n : ℕ) (lam S : ℚ) : IsDyadic (modeCoeff n lam S) :=
  ⟨10*n,⌊(2:ℚ)^(10*n)*(lam/S)⌋,rfl⟩

lemma modeRemainder_dyadic (n : ℕ) {lam S : ℚ}
    (hlam : IsDyadic lam) (hS : IsDyadic S) : IsDyadic (modeRemainder n lam S) :=
  hlam.sub ((modeCoeff_dyadic n lam S).mul hS)

/-- The three actual branches, including mode selection and uniform-label masses. -/
noncomputable def firstModeMass (n Q B d j : ℕ) : ℝ :=
  (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ)/2 *
    ∑ t ∈ Finset.range d, residueProbability Q d j t

noncomputable def secondModeMass (n Q B d j : ℕ) : ℝ :=
  (1/4) * ∑ t ∈ Finset.range d,
    (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t) *
      (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ))

noncomputable def thirdModeMass (n Q B d j : ℕ) : ℝ :=
  (1/4) * (1/(B:ℝ)^2) * (4*(B:ℝ)^2 *
    (modeRemainder n (prescribedMass d) (majorantSum Q B d j):ℝ))

/-- Exact cancellation, not an estimate: Mode 2 fills precisely U-P. -/
lemma first_second_mass {n Q B d j : ℕ} (hB : 0 < B) (hd : 0 < d)
    (hj : Nat.Coprime j d) :
    firstModeMass n Q B d j + secondModeMass n Q B d j =
      (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ) *
      (majorantSum Q B d j:ℝ) := by
  have hB' : (B:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  let c : ℝ := modeCoeff n (prescribedMass d) (majorantSum Q B d j)
  have hs : ∀ t, (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t)*c) =
      2*c*((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t) := by
    intro t
    field_simp
  unfold firstModeMass secondModeMass
  change c/2*(∑ t ∈ Finset.range d, residueProbability Q d j t) +
    1/4*(∑ t ∈ Finset.range d, (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t)*c)) =
        c*(majorantSum Q B d j:ℝ)
  simp_rw [hs]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_residue_permutation hd hj (fun u => (majorant Q B d j u:ℝ))]
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  ring

lemma third_mode_mass {n Q B d j : ℕ} (hB : 0 < B) :
    thirdModeMass n Q B d j =
      (modeRemainder n (prescribedMass d) (majorantSum Q B d j):ℝ) := by
  have hB' : (B:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  unfold thirdModeMass
  field_simp

/-- The exact mass per reduced label, including the d=1, j=0 boundary case. -/
lemma three_mode_mass {n Q B d j : ℕ} (hB : 0 < B) (hd : 0 < d)
    (hj : Nat.Coprime j d) :
    firstModeMass n Q B d j + secondModeMass n Q B d j + thirdModeMass n Q B d j =
      (prescribedMass d:ℝ) := by
  rw [first_second_mass hB hd hj, third_mode_mass hB]
  simp only [modeRemainder, Rat.cast_sub, Rat.cast_mul]
  ring

lemma largeQ_cube (B : ℕ) (hB : 2 ≤ B) : 256*B^3 ≤ B^16 := by
  have h : 256 ≤ B^13 := (by norm_num : 256 ≤ (2:ℕ)^13).trans (Nat.pow_le_pow_left hB 13)
  calc
    _ ≤ B^13*B^3 := Nat.mul_le_mul_right (B^3) h
    _ = _ := by rw [← pow_add]

/-- The artificial discrepancy is a valid probability even at false labels. -/
lemma discrepancy_retention_bounds {B d t : ℕ} (hB : 2 ≤ B) (hd : 0 < d)
    (hdB : d < B) (ht : t < d) (j : ℕ) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    0 ≤ 2*(B:ℝ)^3*((majorant (B^16) B d j ((j*t)%d):ℝ)-
      residueProbability (B^16) d j t)*c ∧
    2*(B:ℝ)^3*((majorant (B^16) B d j ((j*t)%d):ℝ)-
      residueProbability (B^16) d j t)*c ≤ 1 := by
  have hB₀ : 0 < B := by omega
  have hQ₀ : 0 < B^16 := pow_pos hB₀ _
  have hBQ : B ≤ B^16 := (by omega : B ≤ 65*B).trans (largeQ B hB)
  have he := majorant_probability_error hB hd hdB.le (hdB.le.trans hBQ) ht j
  have he₀ : 0 ≤ (majorant (B^16) B d j ((j*t)%d):ℝ)-residueProbability (B^16) d j t :=
    (by positivity : (0:ℝ) ≤ 32/(B^16:ℕ)).trans he.1
  have hq : (256:ℝ)*(B:ℝ)^3 ≤ (B:ℝ)^16 := by exact_mod_cast largeQ_cube B hB
  have hq₀ : (0:ℝ) < (B:ℝ)^16 := by positivity
  have he₁ : (majorant (B^16) B d j ((j*t)%d):ℝ)-residueProbability (B^16) d j t ≤
      128/(B:ℝ)^16 := by
    refine he.2.trans ?_
    simp only [Nat.cast_pow]
    exact div_le_div_of_nonneg_right (by norm_num) hq₀.le
  constructor
  · positivity
  calc
    _ ≤ 2*(B:ℝ)^3*(128/(B:ℝ)^16)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left he₁ (by positivity)) hc₁ hc₀ (by positivity)
    _ = 256*(B:ℝ)^3/(B:ℝ)^16 := by ring
    _ ≤ 1 := (div_le_one hq₀).mpr hq

lemma remainder_retention_bounds {n : ℕ} (hn : 1 ≤ n) {rho : ℝ}
    (hr₀ : 0 ≤ rho) (hr₁ : rho ≤ 2/(2:ℝ)^(10*n)) :
    0 ≤ 4*((2:ℝ)^n)^2*rho ∧ 4*((2:ℝ)^n)^2*rho ≤ 1 := by
  have h : (8:ℝ) ≤ 2^(8*n) := by
    calc
      _ ≤ (2:ℝ)^8 := by norm_num
      _ ≤ 2^(8*n) := pow_le_pow_right₀ (by norm_num) (by omega)
  have he : (2:ℝ)^(10*n) = ((2:ℝ)^n)^2*2^(8*n) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  constructor
  · positivity
  calc
    _ ≤ 4*((2:ℝ)^n)^2*(2/(2:ℝ)^(10*n)) :=
      mul_le_mul_of_nonneg_left hr₁ (by positivity)
    _ = 8/(2:ℝ)^(8*n) := by
      rw [he]
      field_simp
      norm_num
    _ ≤ 1 := (div_le_one (by positivity)).mpr h

end ExactQuantumFactoring.OrderTrial



end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/Exactness.lean =====
namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Integer arithmetic at grid points.  The only root of unity is -i. -/
def minusI : GaussianInt := ⟨0,-1⟩

lemma minusI_cast : (minusI:ℂ) = -Complex.I := by
  simp [minusI, GaussianInt.toComplex_def]

def gridPhaseNumerator (Q y : ℕ) : GaussianInt :=
  ((Q-(4*y)%Q:ℕ):GaussianInt)*minusI^((4*y)/Q) +
    (((4*y)%Q:ℕ):GaussianInt)*minusI^((4*y)/Q+1)

lemma phase_grid_numerator {Q : ℕ} (hQ : 0 < Q) (y : ℕ) :
    phase ((y:ℝ)/Q) = (gridPhaseNumerator Q y:ℂ)/(Q:ℂ) := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQc : (Q:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hr : (4*y)%Q < Q := Nat.mod_lt _ hQ
  have hr' : (0:ℝ) ≤ ((4*y)%Q:ℕ) := Nat.cast_nonneg _
  have hle : (((4*y)%Q:ℕ):ℝ) ≤ Q := by exact_mod_cast hr.le
  have ht₀ : 0 ≤ (((4*y)%Q:ℕ):ℝ)/Q := div_nonneg hr' hQ'.le
  have ht₁ : (((4*y)%Q:ℕ):ℝ)/Q ≤ 1 := (div_le_one hQ').mpr hle
  have he : ((((4*y)/Q:ℕ):ℝ)+(((4*y)%Q:ℕ):ℝ)/Q)/4 = (y:ℝ)/Q := by
    have h := Nat.mod_add_div (4*y) Q
    have h' : (((4*y)%Q:ℕ):ℝ)+(Q:ℝ)*((4*y)/Q:ℕ) = 4*y := by exact_mod_cast h
    field_simp
    nlinarith
  have hg := phase_interpolates (((4*y)/Q:ℕ):ℤ) ht₀ ht₁
  rw [show (((4*y)/Q:ℕ):ℤ)+1 = (((4*y)/Q+1:ℕ):ℤ) by simp] at hg
  simp only [Int.cast_natCast, zpow_natCast] at hg
  rw [he] at hg
  rw [hg]
  simp only [gridPhaseNumerator, map_add, map_sub, map_mul, map_pow, map_natCast,
    minusI_cast, Nat.cast_sub hr.le, Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

/-- A literal finite integer sum, used to prove dyadicity independently of the
bounded-piece evaluator.  This sum is NOT asserted to be polynomial-time. -/
def residueGaussianNumerator (Q d j t : ℕ) : GaussianInt :=
  ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t), gridPhaseNumerator Q (bin Q d j*x)

def residueProbabilityRat (Q d j t : ℕ) : ℚ :=
  ((residueGaussianNumerator Q d j t).norm:ℚ)/(Q:ℚ)^4

lemma residueAmplitude_gaussian {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    residueAmplitude Q d j t = (residueGaussianNumerator Q d j t:ℂ)/(Q:ℂ)^2 := by
  have hph : ∀ x : ℕ, phase ((bin Q d j:ℝ)*x/Q) =
      (gridPhaseNumerator Q (bin Q d j*x):ℂ)/(Q:ℂ) := by
    intro x
    simpa only [Nat.cast_mul] using phase_grid_numerator hQ (bin Q d j*x)
  unfold residueAmplitude
  simp_rw [hph]
  rw [← Finset.sum_div]
  simp only [residueGaussianNumerator, map_sum]
  ring

lemma residueProbabilityRat_cast {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    (residueProbabilityRat Q d j t:ℝ) = residueProbability Q d j t := by
  rw [residueProbability, residueAmplitude_gaussian hQ, norm_div, norm_pow,
    Complex.norm_natCast, div_pow, ← Complex.normSq_eq_norm_sq,
    ← GaussianInt.intCast_real_norm]
  simp only [residueProbabilityRat, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast]
  ring

lemma residueProbabilityRat_nonneg (Q d j t : ℕ) : 0 ≤ residueProbabilityRat Q d j t := by
  unfold residueProbabilityRat
  exact div_nonneg (Int.cast_nonneg (GaussianInt.norm_nonneg _)) (by positivity)

lemma residueProbabilityRat_le_one {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    residueProbabilityRat Q d j t ≤ 1 := by
  have h := residueAmplitude_norm_le hQ d j t
  have h' : (residueProbabilityRat Q d j t:ℝ) ≤ 1 := by
    rw [residueProbabilityRat_cast hQ, residueProbability]
    nlinarith [norm_nonneg (residueAmplitude Q d j t)]
  exact_mod_cast h'

lemma residueProbability_dyadic (b d j t : ℕ) :
    IsDyadic (residueProbabilityRat (2^b) d j t) := by
  refine ⟨b*4,(residueGaussianNumerator (2^b) d j t).norm,?_⟩
  simp only [residueProbabilityRat, Nat.cast_pow, Nat.cast_ofNat, pow_mul]

/-- An explicit 4b-bit denominator, and numerator bounded by that denominator. -/
lemma residueProbability_numerator_bounds {Q : ℕ} (hQ : 0 < Q) (d j t : ℕ) :
    0 ≤ (residueGaussianNumerator Q d j t).norm ∧
      (residueGaussianNumerator Q d j t).norm ≤ (Q:ℤ)^4 := by
  refine ⟨GaussianInt.norm_nonneg _,?_⟩
  have h := residueProbabilityRat_le_one hQ d j t
  have he : ((residueGaussianNumerator Q d j t).norm:ℚ) ≤ (Q:ℚ)^4 := by
    exact (div_le_one (by positivity : (0:ℚ) < (Q:ℚ)^4)).mp h
  exact_mod_cast he

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

noncomputable def phaseLabel (m y : ℕ) : ℂ := Complex.I^(y/m)

lemma phaseLabel_mod (m y : ℕ) : phaseLabel m (y%(4*m)) = phaseLabel m y := by
  unfold phaseLabel
  rw [Nat.mod_mul_left_div_self, ← Complex.I_pow_eq_pow_mod]

lemma phaseLabel_tile {m : ℕ} (hm : 0 < m) (a : ℕ) {u : ℕ} (hu : u < m) :
    phaseLabel m (a*m+u) = Complex.I^a := by
  unfold phaseLabel
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hu, zero_add]

lemma phaseLabel_correlation {m : ℕ} (hm : 0 < m) (a q : ℕ) {u s : ℕ}
    (hu : u < m) (hs : s < m) :
    star (phaseLabel m ((a*m+u+(q*m+s))%(4*m))) * phaseLabel m (a*m+u) =
      if u+s < m then (-Complex.I)^q else (-Complex.I)^(q+1) := by
  rw [phaseLabel_mod, phaseLabel_tile hm a hu]
  have he : a*m+u+(q*m+s) = (a+q)*m+(u+s) := by ring
  rw [he]
  by_cases h : u+s < m
  · rw [ite_eq_left h, phaseLabel_tile hm (a+q) h, pow_add]
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_I]
    have hi : (-Complex.I)^a*Complex.I^a = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((-Complex.I)^a*Complex.I^a)*(-Complex.I)^q := by ring
      _ = _ := by rw [hi, one_mul]
  · have hb : u+s-m < m := by omega
    have he : (a+q)*m+(u+s) = (a+(q+1))*m+(u+s-m) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    rw [ite_eq_right h, he, phaseLabel_tile hm (a+(q+1)) hb, pow_add]
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_I]
    have hi : (-Complex.I)^a*Complex.I^a = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = ((-Complex.I)^a*Complex.I^a)*(-Complex.I)^(q+1) := by ring
      _ = _ := by rw [hi, one_mul]

lemma sum_range_tiles {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a m : ℕ) :
    (∑ y ∈ Finset.range (a*m), f y) =
      ∑ i ∈ Finset.range a, ∑ u ∈ Finset.range m, f (i*m+u) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma sum_if_carry {m s : ℕ} (hs : s ≤ m) (v w : ℂ) :
    (∑ u ∈ Finset.range m, if u+s < m then v else w) = (m-s:ℕ)*v+(s:ℂ)*w := by
  have he := Finset.sum_range_add (fun u => if u+s< m then v else w) (m-s) s
  rw [Nat.sub_add_cancel hs] at he
  rw [he]
  have h₁ : (∑ u ∈ Finset.range (m-s), if u+s< m then v else w) = (m-s:ℕ)*v := by
    calc
      _ = ∑ u ∈ Finset.range (m-s), v := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_left (by have := Finset.mem_range.mp hu; omega)]
      _ = _ := by simp
  have h₂ : (∑ u ∈ Finset.range s, if m-s+u+s< m then v else w) = (s:ℂ)*w := by
    calc
      _ = ∑ u ∈ Finset.range s, w := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_right (by omega)]
      _ = _ := by simp
  rw [h₁,h₂]

/-- Unnormalized correlation of the exactly prepared quarter-step state. -/
noncomputable def phaseOverlapSum (m D : ℕ) : ℂ :=
  ∑ y ∈ Finset.range (4*m), star (phaseLabel m ((y+D)%(4*m))) * phaseLabel m y

lemma phaseOverlapSum_eq {m : ℕ} (hm : 0 < m) (q : ℕ) {s : ℕ} (hs : s < m) :
    phaseOverlapSum m (q*m+s) =
      (4*(m-s):ℕ)*(-Complex.I)^q+(4*s:ℕ)*(-Complex.I)^(q+1) := by
  unfold phaseOverlapSum
  rw [sum_range_tiles]
  have h : ∀ a, (∑ u ∈ Finset.range m,
      star (phaseLabel m ((a*m+u+(q*m+s))%(4*m))) * phaseLabel m (a*m+u)) =
      (m-s:ℕ)*(-Complex.I)^q+(s:ℂ)*(-Complex.I)^(q+1) := by
    intro a
    calc
      _ = ∑ u ∈ Finset.range m, if u+s< m then (-Complex.I)^q else (-Complex.I)^(q+1) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact phaseLabel_correlation hm a q (Finset.mem_range.mp hu) hs
      _ = _ := sum_if_carry hs.le _ _
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Exact overlap, with its direction fixed by the forward shift. -/
lemma phaseOverlap_eq {m : ℕ} (hm : 0 < m) (D : ℕ) :
    phaseOverlapSum m D/(4*(m:ℂ)) = phase ((D:ℝ)/(4*(m:ℝ))) := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hmc : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hs : D%m < m := Nat.mod_lt _ hm
  have hD : D/m*m+D%m=D := by simpa only [Nat.mul_comm] using Nat.div_add_mod D m
  have hov := phaseOverlapSum_eq hm (D/m) hs
  rw [hD] at hov
  have hph := phase_interpolates ((D/m:ℕ):ℤ)
    (div_nonneg (Nat.cast_nonneg (D%m)) hm'.le)
    ((div_le_one hm').mpr (by exact_mod_cast hs.le))
  have he : ((((D/m:ℕ):ℝ)+((D%m:ℕ):ℝ)/m)/4) = (D:ℝ)/(4*(m:ℝ)) := by
    have he' : ((D/m:ℕ):ℝ)*m+((D%m:ℕ):ℝ)=D := by exact_mod_cast hD
    field_simp
    nlinarith
  rw [show ((D/m:ℕ):ℤ)+1 = ((D/m+1:ℕ):ℤ) by simp] at hph
  simp only [Int.cast_natCast, zpow_natCast] at hph
  rw [he] at hph
  rw [hov,hph]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hs.le,
    Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

noncomputable def phaseState (m y : ℕ) : ℂ :=
  (Real.sqrt (4*(m:ℝ)):ℂ)⁻¹ * phaseLabel m y

lemma phaseState_overlap {m : ℕ} (hm : 0 < m) (D : ℕ) :
    (∑ y ∈ Finset.range (4*m), star (phaseState m ((y+D)%(4*m))) * phaseState m y) =
      phase ((D:ℝ)/(4*(m:ℝ))) := by
  have hs : (Real.sqrt (4*(m:ℝ)):ℂ)^2 = 4*(m:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have h (y : ℕ) : star (phaseState m ((y+D)%(4*m))) * phaseState m y =
      (star (phaseLabel m ((y+D)%(4*m))) * phaseLabel m y)/(4*(m:ℂ)) := by
    unfold phaseState
    simp only [star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
    rw [← hs]
    ring
  simp_rw [h]
  rw [← Finset.sum_div]
  exact phaseOverlap_eq hm D

lemma phaseState_normalized {m : ℕ} (hm : 0 < m) :
    (∑ y ∈ Finset.range (4*m), Complex.normSq (phaseState m y)) = 1 := by
  have h := phaseState_overlap hm 0
  have he : ∀ y ∈ Finset.range (4*m),
      star (phaseState m ((y+0)%(4*m)))*phaseState m y =
        (Complex.normSq (phaseState m y):ℂ) := by
    intro y hy
    rw [Nat.add_zero, Nat.mod_eq_of_lt (Finset.mem_range.mp hy)]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [Finset.sum_congr rfl he] at h
  have hz : phase 0=1 := by simpa using phase_zero_quarter (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1)
  simp only [Nat.cast_zero, zero_div, hz] at h
  exact_mod_cast h

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

/-- Source (completion), with its actual downward integer rounding. -/
def completionCoeff (E : ℕ) (z A : ℚ) : ℚ :=
  (⌊(2:ℚ)^E*(z/A)⌋ : ℤ)/(2:ℚ)^E

def completionRemainder (E : ℕ) (z A : ℚ) : ℚ := z-completionCoeff E z A*A

lemma completion_rounding (E : ℕ) {z A : ℚ} (hz : 0 ≤ z) (hA : 0 < A)
    (hzA : z ≤ A) :
    0 ≤ completionCoeff E z A ∧ completionCoeff E z A ≤ 1 ∧
      0 ≤ completionRemainder E z A ∧ completionRemainder E z A < A/2^E := by
  have hD : (0:ℚ) < 2^E := by positivity
  have hx : 0 ≤ (2:ℚ)^E*(z/A) := mul_nonneg hD.le (div_nonneg hz hA.le)
  have hf := Int.floor_le ((2:ℚ)^E*(z/A))
  have hu := Int.lt_floor_add_one ((2:ℚ)^E*(z/A))
  have hfn : (0:ℚ) ≤ (⌊(2:ℚ)^E*(z/A)⌋ : ℤ) :=
    Int.cast_nonneg (Int.floor_nonneg.mpr hx)
  have hc₀ : 0 ≤ completionCoeff E z A := div_nonneg hfn hD.le
  have hc₁ : completionCoeff E z A ≤ z/A := by
    unfold completionCoeff
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have herr : z/A-completionCoeff E z A < 1/(2:ℚ)^E := by
    apply (mul_lt_mul_iff_right₀ hD).mp
    unfold completionCoeff
    rw [mul_sub, mul_div_cancel₀ _ hD.ne', mul_div_cancel₀ _ hD.ne']
    linarith
  have he : completionRemainder E z A = (z/A-completionCoeff E z A)*A := by
    unfold completionRemainder
    rw [sub_mul, div_mul_cancel₀ _ hA.ne']
  refine ⟨hc₀, hc₁.trans ((div_le_one hA).mpr hzA), ?_, ?_⟩
  · rw [he]
    exact mul_nonneg (sub_nonneg.mpr hc₁) hA.le
  · rw [he]
    calc
      _ < (1/(2:ℚ)^E)*A := mul_lt_mul_of_pos_right herr hA
      _ = _ := by ring

/-- Both branch masses include the choice of branch and the guessing probability. -/
lemma completion_mass (W t : ℕ) (s z : ℚ) :
    (1-1/(2:ℚ)^t)*s * completionCoeff (W+t+2) z ((1-1/(2:ℚ)^t)*s) +
    (1/(2:ℚ)^t)*(1/(2:ℚ)^W)*
      (completionRemainder (W+t+2) z ((1-1/(2:ℚ)^t)*s)*(2:ℚ)^W/(1/(2:ℚ)^t)) = z := by
  unfold completionRemainder
  field_simp
  ring

lemma completion_retention_bounds (W t : ℕ) {s z : ℚ}
    (hs₀ : 0 < s) (hs₁ : s ≤ 1) (ht : 0 < t)
    (hz : 0 < z) (hzA : z ≤ (1-1/(2:ℚ)^t)*s) :
    let A := (1-1/(2:ℚ)^t)*s
    let C := completionCoeff (W+t+2) z A
    let R := completionRemainder (W+t+2) z A
    0 ≤ C ∧ C ≤ 1 ∧ 0 ≤ R*(2:ℚ)^W/(1/(2:ℚ)^t) ∧
      R*(2:ℚ)^W/(1/(2:ℚ)^t) < 1/4 := by
  let A := (1-1/(2:ℚ)^t)*s
  have hδ₀ : (0:ℚ) < 1/2^t := by positivity
  have hδ₁ : (1:ℚ)/2^t < 1 := by
    apply (div_lt_one (by positivity : (0:ℚ) < 2^t)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hA : 0 < A := mul_pos (sub_pos.mpr hδ₁) hs₀
  have hA₁ : A ≤ 1 := by
    calc
      _ ≤ 1*s := mul_le_mul_of_nonneg_right (by linarith : 1-1/(2:ℚ)^t ≤ 1) hs₀.le
      _ ≤ 1 := by simpa using hs₁
  have h := completion_rounding (W+t+2) hz.le hA hzA
  dsimp only
  refine ⟨h.1, h.2.1, div_nonneg (mul_nonneg h.2.2.1 (by positivity)) hδ₀.le, ?_⟩
  have hR : completionRemainder (W+t+2) z A < 1/(2:ℚ)^(W+t+2) :=
    h.2.2.2.trans_le (div_le_div_of_nonneg_right hA₁ (by positivity))
  calc
    _ < (1/(2:ℚ)^(W+t+2))*(2:ℚ)^W/(1/(2:ℚ)^t) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hR (by positivity)) hδ₀
    _ = 1/4 := by rw [pow_add, pow_add]; norm_num; field_simp

/-- The second rounding of Section 6, independent of the transition algorithm. -/
def quarterCoeff (J : ℕ) (p : ℚ) : ℚ := completionCoeff (J+2) (1/2) p

def quarterRemainder (J : ℕ) (p : ℚ) : ℚ := 1/4-p*quarterCoeff J p/2

lemma quarter_retention_bounds (J : ℕ) {p : ℚ} (hp₀ : 1/2 < p) (hp₁ : p ≤ 1) :
    0 ≤ quarterCoeff J p ∧ quarterCoeff J p ≤ 1 ∧
      0 ≤ (2:ℚ)^(J+1)*quarterRemainder J p ∧
      (2:ℚ)^(J+1)*quarterRemainder J p < 1/4 := by
  have h := completion_rounding (J+2) (by norm_num : (0:ℚ) ≤ 1/2)
    (by linarith : 0 < p) hp₀.le
  have he : quarterRemainder J p = completionRemainder (J+2) (1/2) p/2 := by
    unfold quarterRemainder quarterCoeff completionRemainder
    ring
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [he]
    exact mul_nonneg (by positivity) (div_nonneg h.2.2.1 (by norm_num))
  · rw [he]
    have hR : completionRemainder (J+2) (1/2) p < 1/(2:ℚ)^(J+2) :=
      h.2.2.2.trans_le (div_le_div_of_nonneg_right hp₁ (by positivity))
    calc
      _ < (2:ℚ)^(J+1)*(1/(2:ℚ)^(J+2)/2) :=
        mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hR (by norm_num)) (by positivity)
      _ = 1/4 := by rw [pow_add, pow_add]; norm_num; field_simp

lemma quarter_mass (J : ℕ) (p : ℚ) :
    (1/2)*p*quarterCoeff J p +
      (1/2)*(1/(2:ℚ)^J)*((2:ℚ)^(J+1)*quarterRemainder J p)=1/4 := by
  unfold quarterRemainder
  rw [pow_succ]
  field_simp
  ring

/-- An explicit elementary discrete bound eliminates a real-calculus asymptotic. -/
lemma step_tenth_power_bound {n : ℕ} (hn : 128 ≤ n) : (n+1)^10 ≤ 2*n^10 := by
  have h₀ : 128*(n+1) ≤ 129*n := by omega
  have h₁ := Nat.pow_le_pow_left h₀ 10
  rw [mul_pow,mul_pow] at h₁
  have hc : 129^10 ≤ 2*128^10 := by norm_num
  have h₂ : 128^10*(n+1)^10 ≤ 128^10*(2*n^10) := by
    calc
      _ ≤ 129^10*n^10 := h₁
      _ ≤ (2*128^10)*n^10 := Nat.mul_le_mul_right _ hc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h₂ (by norm_num)

lemma tenth_power_exponential {n : ℕ} (hn : 128 ≤ n) : 2*n^10 < 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hs := step_tenth_power_bound hn
    calc
      _ ≤ 2*(2*n^10) := Nat.mul_le_mul_left 2 hs
      _ < 2*2^n := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; omega

def knownProbability (n : ℕ) : ℚ := (1-1/(2:ℚ)^n)^(n^10)

lemma knownProbability_bounds {n : ℕ} (hn : 128 ≤ n) :
    1/2 < knownProbability n ∧ knownProbability n ≤ 1 := by
  have hD : (0:ℚ) < 2^n := by positivity
  have hD₁ : (1:ℚ) ≤ 2^n := one_le_pow₀ (by norm_num)
  have hδ : (1:ℚ)/2^n ≤ 1 := (div_le_one hD).mpr hD₁
  have hbin := one_add_mul_le_pow (R:=ℚ)
    (show -2 ≤ -(1/(2:ℚ)^n) by linarith) (n^10)
  have hexp : (2:ℚ)*(n:ℚ)^10 < 2^n := by exact_mod_cast tenth_power_exponential hn
  have hsmall : (n:ℚ)^10/(2:ℚ)^n < 1/2 := by
    apply (div_lt_iff₀ hD).mpr
    linarith
  unfold knownProbability
  constructor
  · simp only [Nat.cast_pow, ← sub_eq_add_neg, mul_neg, mul_one_div] at hbin
    linarith
  · calc
      _ ≤ (1:ℚ)^(n^10) := pow_le_pow_left₀ (by linarith : 0 ≤ 1-1/(2:ℚ)^n)
        (by linarith [le_of_lt (show (0:ℚ) < 1/(2:ℚ)^n by positivity)]) _
      _ = 1 := one_pow _

end ExactQuantumFactoring.Exactness



end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/SuperpositionGates.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

abbrev phaseAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .phase, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _; exact Subsingleton.elim a b⟩

abbrev hadamardAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .hadamard, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _; exact Subsingleton.elim a b⟩

lemma eq_update_iff {q : ℕ} (x y : Basis q) (t : Fin q) (b : Bool) :
    y = Function.update x t b ↔ y t = b ∧ ∀ i, i ≠ t → y i = x i := by
  classical
  constructor
  · rintro rfl
    exact ⟨Function.update_self _ _ _, fun i hi => Function.update_of_ne hi _ _⟩
  · rintro ⟨ht,ho⟩
    funext i
    by_cases hi : i = t
    · subst i; simpa using ht
    · simpa [Function.update_of_ne hi] using ho i hi

lemma phaseAt_matrix {q : ℕ} (t : Fin q) (x y : Basis q) :
    (phaseAt t).matrix y x = if y = x then (if x t then Complex.I else 1) else 0 := by
  classical
  change (if ∀ i : Fin q, (∀ _ : Fin 1, t ≠ i) → y i = x i then
      (plainGate .phase).matrix (List.ofFn (fun _ : Fin 1 => y t))
        (List.ofFn (fun _ : Fin 1 => x t)) else 0) = _
  simp only [Gate.matrix, Gate.baseMatrix, Bool.false_eq_true, ite_false, List.ofFn_succ,
    List.ofFn_zero, Primitive.matrix]
  by_cases he : y = x
  · subst y; simp
  · by_cases ht : y t = x t
    · have ho : ¬ ∀ i : Fin q, t ≠ i → y i = x i := by
        intro hh
        apply he
        funext i
        by_cases hi : t = i
        · subst i; exact ht
        · exact hh i hi
      simp [he, ho]
    · simp [he, ht]

lemma phaseAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (phaseAt t).matrix.mulVec (basisVector x) =
      (if x t then Complex.I else 1) • basisVector x := by
  classical
  rw [matrix_basisVector]
  funext y
  rw [phaseAt_matrix]
  by_cases he : y = x <;> simp [basisVector, he]

lemma phaseSquared_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (programMatrix [phaseAt t, phaseAt t]).mulVec (basisVector x) =
      (if x t then (-1 : ℂ) else 1) • basisVector x := by
  rw [programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec,
    phaseAt_basis, Matrix.mulVec_smul, phaseAt_basis, smul_smul]
  cases x t <;> simp

lemma BooleanProgram.phase_compute_uncompute {q : ℕ} (p : BooleanProgram q)
    (t : Fin q) (x : Basis q) :
    (programMatrix (p.compile ++ [phaseAt t, phaseAt t] ++
      p.compile.reverse.map Instruction.reverse)).mulVec (basisVector x) =
      (if p.eval x t then (-1 : ℂ) else 1) • basisVector x := by
  rw [programMatrix_append, programMatrix_append, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, p.compile_basis x, phaseSquared_basis,
    Matrix.mulVec_smul, p.uncompute x]

lemma hadamardAt_matrix {q : ℕ} (t : Fin q) (x y : Basis q) :
    (hadamardAt t).matrix y x =
      if ∀ i, i ≠ t → y i = x i then
        (if y t && x t then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ) else 0 := by
  classical
  change (if ∀ i : Fin q, (∀ _ : Fin 1, t ≠ i) → y i = x i then
      (plainGate .hadamard).matrix (List.ofFn (fun _ : Fin 1 => y t))
        (List.ofFn (fun _ : Fin 1 => x t)) else 0) = _
  simp only [Gate.matrix, Gate.baseMatrix, Bool.false_eq_true, ite_false, List.ofFn_succ,
    List.ofFn_zero, Primitive.matrix]
  have he : (∀ i, t ≠ i → y i = x i) ↔ (∀ i, i ≠ t → y i = x i) := by
    constructor <;> intro h i hi <;> exact h i (Ne.symm hi)
  simp only [forall_const, he]

lemma hadamardAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (hadamardAt t).matrix.mulVec (basisVector x) =
      (Real.sqrt 2 : ℂ)⁻¹ • (basisVector (Function.update x t false) +
        (if x t then (-1 : ℂ) else 1) • basisVector (Function.update x t true)) := by
  classical
  rw [matrix_basisVector]
  funext y
  rw [hadamardAt_matrix]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector, eq_update_iff]
  by_cases ho : ∀ i, i ≠ t → y i = x i
  · cases hx : x t <;> cases hy : y t <;> simp_all [div_eq_mul_inv]
  · simp [ho]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhasePreparation.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma hadamardAt_apply {q : ℕ} (t : Fin q) (ψ : State q) (y : Basis q) :
    (hadamardAt t).matrix.mulVec ψ y =
      (ψ (Function.update y t false) +
        (if y t then (-1 : ℂ) else 1) * ψ (Function.update y t true)) / (Real.sqrt 2 : ℂ) := by
  classical
  change (∑ x, (hadamardAt t).matrix y x * ψ x) = _
  have hne : Function.update y t false ≠ Function.update y t true := by
    intro h; have := congrFun h t; simp at this
  rw [Finset.sum_eq_add (Function.update y t false) (Function.update y t true) hne]
  · rw [hadamardAt_matrix, hadamardAt_matrix]
    have h₀ : ∀ i, i ≠ t → y i = Function.update y t false i := by
      intro i hi; simp [Function.update_of_ne hi]
    have h₁ : ∀ i, i ≠ t → y i = Function.update y t true i := by
      intro i hi; simp [Function.update_of_ne hi]
    rw [ite_eq_left h₀, ite_eq_left h₁]
    simp only [Function.update_self, Bool.and_false, Bool.false_eq_true, ite_false, Bool.and_true]
    ring
  · intro x _ hx
    rw [hadamardAt_matrix]
    suffices ¬ ∀ i, i ≠ t → y i = x i by rw [ite_eq_right this, zero_mul]
    intro ho
    have he : x = Function.update y t (x t) := by
      apply (eq_update_iff ..).2
      exact ⟨rfl, fun i hi => (ho i hi).symm⟩
    cases ht : x t
    · exact hx.1 (ht ▸ he)
    · exact hx.2 (ht ▸ he)
  · simp
  · simp

lemma phaseAt_apply {q : ℕ} (t : Fin q) (ψ : State q) (y : Basis q) :
    (phaseAt t).matrix.mulVec ψ y = (if y t then Complex.I else 1) * ψ y := by
  classical
  change (∑ x, (phaseAt t).matrix y x * ψ x) = _
  rw [Finset.sum_eq_single y]
  · simp [phaseAt_matrix]
  · intro x _ h; simp [phaseAt_matrix, Ne.symm h]
  · simp

/-- Hadamards on increasing physical wires; no multi-qubit gate abbreviation. -/
def hadamardPrefix (q : ℕ) : (k : ℕ) → k ≤ q → List (Instruction q)
  | 0, _ => []
  | k+1, h => hadamardPrefix q k (by omega) ++ [hadamardAt ⟨k, by omega⟩]

lemma hadamardPrefix_length (q k : ℕ) (h : k ≤ q) : (hadamardPrefix q k h).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [hadamardPrefix, ih]

lemma hadamardPrefix_zero (q k : ℕ) (h : k ≤ q) :
    (programMatrix (hadamardPrefix q k h)).mulVec (basisVector (fun _ => false)) =
      (fun y => if ∀ i : Fin q, k ≤ i.val → y i = false then (Real.sqrt 2 : ℂ)⁻¹ ^ k else 0) := by
  classical
  induction k with
  | zero =>
    rw [hadamardPrefix, programMatrix_nil, Matrix.one_mulVec]
    funext y
    simp only [basisVector, pow_zero, Nat.zero_le, forall_const]
    have : y = (fun _ => false) ↔ ∀ i, y i = false := by
      constructor
      · rintro rfl; simp
      · exact funext
    simp only [this]
  | succ k ih =>
    rw [hadamardPrefix, programMatrix_append, programMatrix_singleton,
      ← Matrix.mulVec_mulVec, ih (by omega)]
    funext y
    rw [hadamardAt_apply]
    have hfalse : (∀ i : Fin q, k ≤ i.val → Function.update y ⟨k, by omega⟩ false i = false) ↔
        (∀ i : Fin q, k+1 ≤ i.val → y i = false) := by
      constructor
      · intro hh i hi
        have hn : i ≠ (⟨k, by omega⟩ : Fin q) := by intro he; have hh := congrArg Fin.val he; change i.val = k at hh; omega
        simpa [Function.update_of_ne hn] using hh i (by omega)
      · intro hh i hi
        by_cases he : i.val = k
        · have he' : i = (⟨k, by omega⟩ : Fin q) := Fin.ext he
          simp [he']
        · rw [Function.update_of_ne (by intro he'; exact he (congrArg Fin.val he'))]
          exact hh i (by omega)
    have htrue : ¬ ∀ i : Fin q, k ≤ i.val → Function.update y ⟨k, by omega⟩ true i = false := by
      intro hh
      have := hh ⟨k, by omega⟩ le_rfl
      simp at this
    simp only [hfalse, ite_eq_right htrue, mul_zero, add_zero]
    split_ifs <;> simp [pow_succ, div_eq_mul_inv]

lemma hadamards_zero (q : ℕ) :
    (programMatrix (hadamardPrefix q q le_rfl)).mulVec (basisVector (fun _ => false)) =
      fun _ => (Real.sqrt 2 : ℂ)⁻¹ ^ q := by
  rw [hadamardPrefix_zero]
  funext y
  rw [ite_eq_left (by intro i hi; exact False.elim (Nat.not_le.mpr i.isLt hi))]

/-- The exact phase-state preparation from Section 3.1: H on every wire,
Z=S² on the most significant wire, and S on the next wire. -/
def preparePhase (b : ℕ) (hb : 2 ≤ b) : List (Instruction b) :=
  hadamardPrefix b b le_rfl ++
    [phaseAt ⟨b-1, by omega⟩, phaseAt ⟨b-1, by omega⟩, phaseAt ⟨b-2, by omega⟩]

lemma preparePhase_length (b : ℕ) (hb : 2 ≤ b) : (preparePhase b hb).length = b+3 := by
  simp [preparePhase, hadamardPrefix_length]

lemma preparePhase_correct (b : ℕ) (hb : 2 ≤ b) (y : Basis b) :
    (programMatrix (preparePhase b hb)).mulVec (basisVector (fun _ => false)) y =
      (Real.sqrt 2 : ℂ)⁻¹ ^ b *
        (if y ⟨b-1, by omega⟩ then (-1 : ℂ) else 1) *
        (if y ⟨b-2, by omega⟩ then Complex.I else 1) := by
  rw [preparePhase, programMatrix_append, ← Matrix.mulVec_mulVec, hadamards_zero]
  rw [programMatrix_cons, programMatrix_cons, programMatrix_singleton,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [phaseAt_apply, phaseAt_apply, phaseAt_apply]
  cases y ⟨b-1, by omega⟩ <;> cases y ⟨b-2, by omega⟩ <;> simp <;> ring_nf <;> simp [Complex.I_sq]

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/PhasePreparationConnection.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma sqrt_two_pow (b : ℕ) : Real.sqrt ((2:ℝ)^b) = Real.sqrt 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

lemma hadamard_normalization (b : ℕ) :
    (Real.sqrt 2 : ℂ)⁻¹ ^ b = (Real.sqrt ((2:ℝ)^b) : ℂ)⁻¹ := by
  rw [sqrt_two_pow, Complex.ofReal_pow, inv_pow]

lemma preparePhase_label (b : ℕ) (y : Basis (b+2)) :
    (programMatrix (preparePhase (b+2) (by omega))).mulVec
        (basisVector (fun _ => false)) y =
      OrderTrial.phaseState (2^b) (bitsValue y).toNat := by
  rw [preparePhase_correct, hadamard_normalization]
  unfold OrderTrial.phaseState OrderTrial.phaseLabel
  rw [bitsValue_quarter]
  have he : (4:ℝ)*(2^b:ℕ) = (2:ℝ)^(b+2) := by push_cast; ring
  rw [he]
  have h₁ : (⟨b+2-1, by omega⟩ : Fin (b+2)) = Fin.last (b+1) := Fin.ext (by simp)
  have h₂ : (⟨b+2-2, by omega⟩ : Fin (b+2)) = (Fin.last b).castSucc := Fin.ext (by simp)
  rw [h₁, h₂]
  cases y (Fin.last (b+1)) <;> cases y (Fin.last b).castSucc <;>
    simp

/-- The physical wire basis is explicitly identified with the natural residue
labels; no implicit change in bit order is hidden in the overlap theorem. -/
def basisNumber (b : ℕ) : Basis b ≃ Fin (2^b) :=
  (bitsEquiv b).trans BitVec.equivFin.toEquiv

lemma basisNumber_val (b : ℕ) (x : Basis b) :
    (basisNumber b x).val = (bitsValue x).toNat := rfl

lemma basis_sum_range (b : ℕ) (f : ℕ → ℂ) :
    (∑ x : Basis b, f (bitsValue x).toNat) = ∑ i ∈ Finset.range (2^b), f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact (basisNumber b).sum_comp (fun i => f i.val)

noncomputable def preparedPhase (b : ℕ) : State (b+2) :=
  (programMatrix (preparePhase (b+2) (by omega))).mulVec (basisVector (fun _ => false))

lemma preparedPhase_overlap (b D : ℕ) :
    (∑ y : Basis (b+2),
      star (OrderTrial.phaseState (2^b) (((bitsValue y).toNat+D) % 2^(b+2))) *
        preparedPhase b y) = OrderTrial.phase ((D:ℝ)/(2:ℝ)^(b+2)) := by
  simp only [preparedPhase, preparePhase_label]
  rw [basis_sum_range (b+2) (fun v =>
    star (OrderTrial.phaseState (2^b) ((v+D)%2^(b+2))) * OrderTrial.phaseState (2^b) v)]
  have he : 2^(b+2) = 4*2^b := by ring
  rw [he, OrderTrial.phaseState_overlap (by positivity)]
  congr 1
  push_cast
  ring

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/BitResidue.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The fixed little-endian physical representation of a modular residue. -/
def basisResidue (b : ℕ) : Basis b ≃ ZMod (2^b) :=
  (basisNumber b).trans (ZMod.finEquiv (2^b)).toEquiv

lemma finEquiv_val {n : ℕ} [NeZero n] (z : Fin n) :
    (ZMod.finEquiv n z).val = z.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

lemma basisResidue_val (b : ℕ) (x : Basis b) :
    (basisResidue b x).val = (bitsValue x).toNat := by
  exact finEquiv_val _

lemma basisResidue_eq (b : ℕ) (x : Basis b) :
    basisResidue b x = ((bitsValue x).toNat : ZMod (2^b)) := by
  rw [← basisResidue_val, ZMod.natCast_zmod_val]

lemma bitsValue_residue (b : ℕ) (z : ZMod (2^b)) :
    (bitsValue ((basisResidue b).symm z)).toNat = z.val := by
  rw [← basisResidue_val, Equiv.apply_symm_apply]

lemma basisResidue_bits (b : ℕ) (v : BitVec b) :
    basisResidue b (fun i => v.getLsbD i.val) = (v.toNat : ZMod (2^b)) := by
  rw [basisResidue_eq, bitsValue_bits]

lemma bitsValue_residue_add (b : ℕ) (z : ZMod (2^b)) (d : Basis b) :
    (fun i : Fin b => (bitsValue ((basisResidue b).symm z)+bitsValue d).getLsbD i.val) =
      (basisResidue b).symm (z+basisResidue b d) := by
  apply (basisResidue b).injective
  rw [basisResidue_bits, Equiv.apply_symm_apply, BitVec.toNat_add]
  rw [ZMod.natCast_mod, Nat.cast_add, bitsValue_residue, ZMod.natCast_zmod_val,
    basisResidue_eq]

lemma basisResidue_zero (b : ℕ) : basisResidue b (fun _ => false) = 0 := by
  rw [basisResidue_eq]
  have h : bitsValue (fun _ : Fin b => false) = (0 : BitVec b) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (fun _ : Fin b => false)).getLsbD i = false from bitsValue_bit _ ⟨i,hi⟩]
    simp
  rw [h]
  simp

end ExactQuantumFactoring


end

end OAI

-- ===== Adapted from lean/OAI/Computability/QuantumFactoring/HadamardAction.lean =====
namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma hadamardAt_symmetric {q : ℕ} (j : Fin q) (x y : Basis q) :
    (hadamardAt j).matrix x y = (hadamardAt j).matrix y x := by
  rw [hadamardAt_matrix, hadamardAt_matrix]
  have h : (∀ i, i ≠ j → x i = y i) ↔ (∀ i, i ≠ j → y i = x i) := by
    constructor <;> intro h i hi <;> exact (h i hi).symm
  simp only [h, Bool.and_comm]

lemma hadamardAt_apply_direct_sum {q : ℕ} (j : Fin q) (ψ : State q) (x : Basis q) :
    (hadamardAt j).matrix.mulVec ψ x =
      (ψ (Function.update x j false) +
        (if x j then (-1:ℂ) else 1)*ψ (Function.update x j true)) / (Real.sqrt 2:ℂ) := by
  classical
  have h (y : Basis q) := congrFun (hadamardAt_basis j x) y
  rw [matrix_basisVector] at h
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector] at h
  change (∑ y, (hadamardAt j).matrix x y * ψ y) = _
  simp_rw [hadamardAt_symmetric j x, h]
  simp only [mul_add, add_mul, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  cases x j <;> simp <;> ring

noncomputable def localHadamard {A : Type*} [Fintype A] {b : ℕ} (j : Fin b) :
    Matrix (Basis b × A) (Basis b × A) ℂ := by
  classical
  exact fun v u => if v.2=u.2 then (hadamardAt j).matrix v.1 u.1 else 0

lemma localHadamard_apply {A : Type*} [Fintype A] {b : ℕ} (j : Fin b)
    (ψ : Basis b × A → ℂ) (v : Basis b × A) :
    (localHadamard (A:=A) j).mulVec ψ v =
      (ψ (Function.update v.1 j false,v.2) +
        (if v.1 j then (-1:ℂ) else 1)*ψ (Function.update v.1 j true,v.2)) /
          (Real.sqrt 2:ℂ) := by
  classical
  change (∑ u : Basis b × A, (if v.2=u.2 then (hadamardAt j).matrix v.1 u.1 else 0) * ψ u) = _
  simp only [Fintype.sum_prod_type, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simpa only [Matrix.mulVec, dotProduct, ite_mul] using
    hadamardAt_apply_direct_sum j (fun d => ψ (d,v.2)) v.1

lemma localHadamard_basis {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ} (j : Fin b)
    (u : Basis b × A) :
    (fun v => localHadamard (A:=A) j v u) =
      (Real.sqrt 2:ℂ)⁻¹ • (basisVector (Function.update u.1 j false,u.2) +
        (if u.1 j then (-1:ℂ) else 1) • basisVector (Function.update u.1 j true,u.2)) := by
  classical
  funext v
  have h := congrFun (hadamardAt_basis j u.1) v.1
  rw [matrix_basisVector] at h
  simp only [localHadamard, Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisVector,
    Prod.ext_iff] at h ⊢
  by_cases hv : v.2=u.2
  · simp only [hv, and_true, ite_true]
    exact h
  · simp [hv]

/-- Logical H on data is physically H on the corresponding encoded wire,
provided the embedding preserves that bit and its two updates. -/
lemma encoded_hadamard {A : Type*} [Fintype A] [DecidableEq A] {b q : ℕ}
    (e : Basis b × A → Basis q) (j : Fin b) (t : Fin q)
    (hbit : ∀ u, e u t = u.1 j)
    (hupdate : ∀ u c, Function.update (e u) t c = e (Function.update u.1 j c,u.2))
    (ψ : Basis b × A → ℂ) :
    (hadamardAt t).matrix.mulVec (encodeState e ψ) =
      encodeState e ((localHadamard (A:=A) j).mulVec ψ) := by
  apply matrix_encodeState
  intro u
  rw [hadamardAt_basis, localHadamard_basis, hbit, hupdate, hupdate,
    encodeState_smul, encodeState_add, encodeState_smul, encodeState_basis, encodeState_basis]

end ExactQuantumFactoring


end

end OAI


