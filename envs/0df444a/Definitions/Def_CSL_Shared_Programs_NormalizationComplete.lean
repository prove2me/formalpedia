-- Prove2me | Definitions.Def_CSL_Shared_Programs_NormalizationComplete
-- name    : CSL_Shared_Programs_NormalizationComplete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:44:24.986804+00:00
-- url     : https://prove2.me/theorems/deef529b-4b8b-4304-91a0-d77d73a67027
-- title:
--   Coded sorting library: Shared / Programs / NormalizationComplete
-- statement:
--   Module `CodedSorting.Shared.Programs.NormalizationComplete` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Numerical parameters of the finite circuit. The definitions calculate stream counts and total edge lengths, and Lean checks the arithmetic relations used in the exponent bound.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.NormalizationComplete

import Definitions.Def_CSL_Compat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_CSL_Interchange_Framework_Memory_LayoutMachine

section Parameters
/-! Numerical parameters of the finite circuit. The definitions calculate stream counts and total edge lengths, and Lean checks the arithmetic relations used in the exponent bound. 





-/

namespace CSL.Parameters

def d : ℕ := 46
def v : ℕ := Nat.choose d 3
def z : ℕ := 3 * Nat.choose (d - 3) 2
def m : ℕ := d ^ 3
def W : ℕ := 2 * v ^ 3 + 3 * v ^ 2 * (v * z + d)
def delta : ℕ := 3 * v ^ 2 * d ^ 2
def S : ℕ := W * m - v ^ 3 + 2 * delta

def eta : ℚ := 9 / 43518487588
def epsilon : ℚ := 18 / 1000000000000

theorem v_value : v = 15180 := by
  norm_num [v, d, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
theorem z_value : z = 2709 := by
  norm_num [z, d, Nat.choose_two_right]
theorem m_value : m = 97336 := by norm_num [m, d]

theorem W_value : W = 28434979789999200 := by
  norm_num [W, v_value, z_value, d]

theorem delta_value : delta = 1462784875200 := by
  norm_num [delta, v_value, d]

theorem S_value : S = 2767747192266968049600 := by
  norm_num [S, W_value, m_value, v_value, delta_value]

theorem strict_integer_gap : S < W * m := by
  norm_num [S_value, W_value, m_value]

theorem integer_gap_value : W * m - S = 572394081600 := by
  norm_num [W_value, m_value, S_value]

theorem eta_identity : (1 : ℚ) - (S : ℚ) / ((W : ℚ) * (m : ℚ)) = eta := by
  norm_num [S_value, W_value, m_value, eta]

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem epsilon_pos : 0 < epsilon := by norm_num [epsilon]
theorem epsilon_lt_one : epsilon < 1 := by norm_num [epsilon]

/-- The second exact rational inequality used in the parameter appendix. -/
theorem logarithm_margin_certificate :
    (11487 / 1000 : ℚ) * epsilon < eta := by
  norm_num [epsilon, eta]

/-- The first exact rational inequality used in the parameter appendix. -/
theorem exponential_series_certificate :
    (46 : ℚ) < ∑ j ∈ Finset.range 13,
      (3829 / 1000 : ℚ) ^ j / (Nat.factorial j : ℚ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Strict rate separation of the first explicitly stated finite block length. -/
theorem finite_blocklength_rate :
    (1 : ℚ) - eta < 120884687720 / (120884687720 + 25 : ℚ) := by
  norm_num [eta]

/-- Strict rate separation after subdividing each edge once. -/
theorem subdivided_blocklength_rate :
    (1 : ℚ) - eta < 241769375439 / (241769375439 + 50 : ℚ) := by
  norm_num [eta]

/-- The coefficient which occurs after normalizing by the scan volume. -/
theorem normalized_volume_multiplier :
    (S : ℚ) / W = (m : ℚ) * (1 - eta) := by
  norm_num [S_value, W_value, m_value, eta]

/-- Positivity of the polynomial used for every d ≥ 39 in Section 4.3. -/
theorem general_saving_polynomial (x : ℚ) (hx : 39 ≤ x) :
    0 < x / 6 * (x ^ 2 - 39 * x + 2) := by
  have hp : 0 ≤ x * (x - 39) := mul_nonneg (by linarith) (by linarith)
  have hfactor : 0 < x ^ 2 - 39 * x + 2 := by nlinarith
  exact mul_pos (by linarith) hfactor

/-- The Taylor certificate gives the real logarithm bound, not just an
approximate floating-point calculation. -/
theorem logarithm_bound : Real.log (m : ℝ) < 11487 / 1000 := by
  have hs : (46 : ℝ) < ∑ j ∈ Finset.range 13,
      (3829 / 1000 : ℝ) ^ j / (Nat.factorial j : ℝ) := by
    have hc := (Rat.cast_lt (K := ℝ)).2 exponential_series_certificate
    push_cast at hc
    exact hc
  have hexp : (46 : ℝ) < Real.exp (3829 / 1000) :=
    lt_of_lt_of_le hs (Real.sum_le_exp_of_nonneg (by norm_num) 13)
  have hlog : Real.log 46 < (3829 / 1000 : ℝ) :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 46)).2 hexp
  have hm : (m : ℝ) = (46 : ℝ) ^ 3 := by norm_num [m, d]
  rw [hm, Real.log_pow]
  norm_num
  linarith

theorem epsilon_log_lt_eta : (epsilon : ℝ) * Real.log (m : ℝ) < (eta : ℝ) := by
  have heps : (0 : ℝ) < (epsilon : ℝ) := by exact_mod_cast epsilon_pos
  have h1 := mul_lt_mul_of_pos_left logarithm_bound heps
  have h2 : (11487 / 1000 : ℝ) * (epsilon : ℝ) < (eta : ℝ) := by
    norm_num [epsilon, eta]
  nlinarith

/-- The actual strict exponent inequality used in Section 5. -/
theorem strict_exponent_gap :
    (S : ℝ) / (W : ℝ) < (m : ℝ) ^ (1 - (epsilon : ℝ)) := by
  have hm : (0 : ℝ) < (m : ℝ) := by norm_num [m_value]
  have hid : (S : ℝ) / (W : ℝ) = (m : ℝ) * (1 - (eta : ℝ)) := by
    norm_num [S_value, W_value, m_value, eta]
  have hsmall : 1 - (eta : ℝ) < Real.exp (-(epsilon : ℝ) * Real.log (m : ℝ)) := by
    have hexp := Real.add_one_le_exp (-(epsilon : ℝ) * Real.log (m : ℝ))
    have hlog := epsilon_log_lt_eta
    linarith
  calc
    (S : ℝ) / (W : ℝ) = (m : ℝ) * (1 - (eta : ℝ)) := hid
    _ < (m : ℝ) * Real.exp (-(epsilon : ℝ) * Real.log (m : ℝ)) :=
      mul_lt_mul_of_pos_left hsmall hm
    _ = (m : ℝ) ^ (1 - (epsilon : ℝ)) := by
      rw [Real.rpow_def_of_pos hm]
      have hsplit : Real.log (m : ℝ) * (1 - (epsilon : ℝ)) =
          Real.log (m : ℝ) + (-(epsilon : ℝ) * Real.log (m : ℝ)) := by ring
      rw [hsplit, Real.exp_add, Real.exp_log hm]

end CSL.Parameters
end Parameters

section NormalizationLogs
/-! Explicit logarithmic comparison constants for the integer-rounded memory
and block parameters. These facts do not assume the target sorting bound. -/

namespace CSL.NormalizationLogs

open Normalization

theorem log_scale_bound {x y c : ℝ} (hx : 0 < x) (hy : 2 ≤ y) (hc : 1 ≤ c)
    (hxy : x ≤ c*y) :
    Real.log x ≤ (1 + Real.log c / Real.log 2) * Real.log y := by
  have hy0 : 0 < y := by linarith
  have hc0 : 0 < c := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hfactor : 0 ≤ Real.log c / Real.log 2 := div_nonneg hlogc hlog2.le
  have hm := mul_le_mul_of_nonneg_left hlogy hfactor
  have he : (Real.log c / Real.log 2) * Real.log 2 = Real.log c :=
    div_mul_cancel₀ _ (ne_of_gt hlog2)
  rw [he] at hm
  calc
    Real.log x ≤ Real.log (c*y) := Real.log_le_log hx hxy
    _ = Real.log c + Real.log y := Real.log_mul (ne_of_gt hc0) (ne_of_gt hy0)
    _ ≤ (1 + Real.log c / Real.log 2) * Real.log y := by nlinarith only [hm]

theorem log_eight_factor : (1 : ℝ) + Real.log 8 / Real.log 2 = 4 := by
  have he : Real.log 8 = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  rw [he]
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  <;> ring

theorem memory_floor_bounds (M : ℕ) (hM : 8 ≤ M) :
    2 ≤ M/4 ∧ M/4 ≤ M ∧ M ≤ 8*(M/4) := by omega

theorem ratio_lower (M B K : ℕ) (hM : 8 ≤ M) (hB : 0 < B) :
    (M : ℝ)/(B : ℝ) ≤ 8*((M/4 : ℕ) : ℝ)/(logicalBlockSize B K : ℝ) := by
  have hb := logical_block_positive B K
  have hbB := logical_block_le_physical B K hB
  have hM8 := (memory_floor_bounds M hM).2.2
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hbr : 0 < (logicalBlockSize B K : ℝ) := by exact_mod_cast hb
  have hbBr : (logicalBlockSize B K : ℝ) ≤ (B : ℝ) := by exact_mod_cast hbB
  have hM8r : (M : ℝ) ≤ 8*((M/4 : ℕ) : ℝ) := by exact_mod_cast hM8
  apply (div_le_div_iff₀ hBr hbr).2
  calc
    (M : ℝ)*(logicalBlockSize B K : ℝ) ≤ (M : ℝ)*(B : ℝ) :=
      mul_le_mul_of_nonneg_left hbBr (by positivity)
    _ ≤ 8*((M/4 : ℕ) : ℝ)*(B : ℝ) := mul_le_mul_of_nonneg_right hM8r hBr.le

theorem ratio_upper (M B K : ℕ) (hB : 0 < B) (hK : 0 < K) :
    ((M/4 : ℕ) : ℝ)/(logicalBlockSize B K : ℝ) ≤ (2*K : ℝ)*((M : ℝ)/(B : ℝ)) := by
  have hb := logical_block_positive B K
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hbr : 0 < (logicalBlockSize B K : ℝ) := by exact_mod_cast hb
  have hex : (B : ℝ) ≤ (2*K : ℝ)*(logicalBlockSize B K : ℝ) := by
    exact_mod_cast block_expansion_bound B K hK
  have hM : ((M/4 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.div_le_self M 4
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hbr hBr).2
  calc
    ((M/4 : ℕ) : ℝ)*(B : ℝ) ≤ (M : ℝ)*(B : ℝ) := mul_le_mul_of_nonneg_right hM hBr.le
    _ ≤ (M : ℝ)*((2*K : ℝ)*(logicalBlockSize B K : ℝ)) :=
      mul_le_mul_of_nonneg_left hex (by positivity)
    _ = (2*K : ℝ)*(M : ℝ)*(logicalBlockSize B K : ℝ) := by ring

theorem normalized_ratio_ge_two (M B K : ℕ) (hM : 8 ≤ M) (hK : 8 ≤ K)
    (hB : B ≤ M) :
    (2 : ℝ) ≤ ((M/4 : ℕ) : ℝ)/(logicalBlockSize B K : ℝ) := by
  have hb : 0 < (logicalBlockSize B K : ℝ) := by
    exact_mod_cast logical_block_positive B K
  apply (le_div_iff₀ hb).2
  exact_mod_cast normalized_ratio M B 2 K hK hM hB

theorem normalized_log_ratio (M B K : ℕ) (hM : 8 ≤ M) (hK : 8 ≤ K)
    (hB : 0 < B) (hMB : 2*B ≤ M) :
    Real.log ((M : ℝ)/(B : ℝ)) / 4 ≤
      Real.log (((M/4 : ℕ) : ℝ)/(logicalBlockSize B K : ℝ)) ∧
    Real.log (((M/4 : ℕ) : ℝ)/(logicalBlockSize B K : ℝ)) ≤
      (1 + Real.log (2*K : ℝ) / Real.log 2) * Real.log ((M : ℝ)/(B : ℝ)) := by
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : (2 : ℝ) ≤ (M : ℝ)/(B : ℝ) := by
    apply (le_div_iff₀ hBr).2
    exact_mod_cast hMB
  have hy := normalized_ratio_ge_two M B K hM hK (by omega)
  constructor
  · have hb := log_scale_bound (x := (M : ℝ)/(B : ℝ)) (by linarith) hy
      (c := 8) (by norm_num) (by simpa only [mul_div_assoc] using ratio_lower M B K hM hB)
    rw [log_eight_factor] at hb
    linarith
  · apply log_scale_bound (by linarith) hx
    · have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    · exact ratio_upper M B K hB (by omega)

theorem normalized_log_memory (M : ℕ) (hM : 8 ≤ M) :
    Real.log (M : ℝ)/4 ≤ Real.log ((M/4 : ℕ) : ℝ) ∧
      Real.log ((M/4 : ℕ) : ℝ) ≤ Real.log (M : ℝ) := by
  have hs := memory_floor_bounds M hM
  have hy : (2 : ℝ) ≤ ((M/4 : ℕ) : ℝ) := by exact_mod_cast hs.1
  have hx : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hxy : (M : ℝ) ≤ 8*((M/4 : ℕ) : ℝ) := by exact_mod_cast hs.2.2
  have hlog := log_scale_bound hx hy (by norm_num : (1 : ℝ) ≤ 8) hxy
  rw [log_eight_factor] at hlog
  refine ⟨by linarith, Real.log_le_log (by linarith) ?_⟩
  exact_mod_cast hs.2.1

end CSL.NormalizationLogs
end NormalizationLogs

section NormalizationComplete
/-! Appendix A's block-size normalization: a single fixed choice of constants
simultaneously supplies the actual simulator, compact-layout conversion,
memory allowance, fixed disk expansion and logarithmic comparisons. -/

namespace CSL.NormalizationComplete

open Normalization NormalizationLogs LayoutConversion

variable {Value : Type*} {L : ℕ}

/-- This view changes the type of a block address; it moves no data. -/
def blockView (D B : ℕ) (disk : BlockReflection.Disk Value) : Normalization.Disk D B Value :=
  fun j i => disk (j.val*B+i.val)

def flattenBlocks (D B : ℕ) (hB : 0 < B) (padding : Value)
    (disk : Normalization.Disk D B Value) : BlockReflection.Disk Value := fun y =>
  if h : y/B < D then disk ⟨y/B,h⟩ ⟨y%B,Nat.mod_lt _ hB⟩ else padding

@[simp] theorem flattenBlocks_at (D B : ℕ) (hB : 0 < B) (padding : Value)
    (disk : Normalization.Disk D B Value) (j : Fin D) (i : Fin B) :
    flattenBlocks D B hB padding disk (j.val*B+i.val) = disk j i := by
  have hd : (j.val*B+i.val)/B=j.val := by
    rw [Nat.mul_comm j.val B, Nat.mul_add_div hB, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  have hm : (j.val*B+i.val)%B=i.val := by simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  simp only [flattenBlocks, hd, hm, dif_pos j.isLt, Fin.eta]

def physicalInput (source target : BlockReflection.Disk Value) (padding : Value)
    (ram : Words L Value) (D B b : ℕ) (hB : 0 < B) : PhysicalState L B D Value :=
  ⟨ram, fun _ => padding,
    blockView D B (expandRun source padding B b hB D ⟨target,[]⟩).disk⟩

theorem physicalInput_represents (source target : BlockReflection.Disk Value) (padding : Value)
    (ram : Words L Value) (D B b : ℕ) (hB : 0 < B) (hb : b ≤ B) :
    Represents hb (⟨ram,blockView D b source⟩ : LogicalState L b D Value)
      (physicalInput source target padding ram D B b hB) := by
  refine ⟨rfl, ?_⟩
  intro j
  funext i
  exact (expanded_representation source padding B b D hB hb target j i).symm

/-- End-to-end conversion, arbitrary data-dependent program execution, and
conversion of THAT program's output back to the compact layout. -/
theorem simulation_with_layout (source target₁ target₂ : BlockReflection.Disk Value)
    (padding : Value) (ram : Words L Value) (D B b : ℕ) (hB : 0 < B) (hb : b ≤ B)
    (policy : Policy L b D Value) (fuel : ℕ) :
    let initial : LogicalState L b D Value := ⟨ram, blockView D b source⟩
    let logical := runLogical policy fuel initial
    let physical := runPhysical hb padding policy fuel
      (physicalInput source target₁ padding ram D B b hB)
    let restored := compactRun (flattenBlocks D B hB padding physical.1.disk)
      B b hB hb D ⟨target₂, []⟩
    (∀ j : Fin D, ∀ i : Fin b, restored.disk (j.val*b+i.val) = logical.1.disk j i) ∧
      (expandRun source padding B b hB D ⟨target₁, []⟩).trace.length +
        physical.2 + restored.trace.length = logical.2 + 8*D := by
  try dsimp
  have href := run_represents_and_cost hb padding policy fuel
    (⟨ram, blockView D b source⟩ : LogicalState L b D Value)
    (physicalInput source target₁ padding ram D B b hB)
    (physicalInput_represents source target₁ padding ram D B b hB hb)
  constructor
  · intro j i
    rw [compactRun_correct _ B b D hB hb _ j.val j.isLt i]
    have he := flattenBlocks_at D B hB padding
      (runPhysical hb padding policy fuel
        (physicalInput source target₁ padding ram D B b hB)).1.disk j (i.castLE hb)
    change flattenBlocks D B hB padding _ (j.val*B+i.val) = _ at he
    rw [he]
    exact (congrFun (href.1.2 j) i).symm
  · rw [expandRun_cost, compactRun_cost, ← href.2]
    simp only [List.length_nil, Nat.zero_add]
    omega

/-- Input occupies only nIn logical blocks. The uninitialized scratch region
is represented by the arbitrary backing disk; no zeroing pass is assumed. -/
def liveLogicalInput (source backing : BlockReflection.Disk Value) (ram : Words L Value)
    (D B b nIn : ℕ) : LogicalState L b D Value :=
  ⟨ram, fun j i => if j.val < nIn then source (j.val*b+i.val) else backing (j.val*B+i.val)⟩

def livePhysicalInput (source backing : BlockReflection.Disk Value) (padding : Value)
    (ram : Words L Value) (D B b nIn : ℕ) (hB : 0 < B) : PhysicalState L B D Value :=
  ⟨ram,fun _ => padding,
    blockView D B (expandRun source padding B b hB nIn ⟨backing,[]⟩).disk⟩

theorem liveInput_represents (source backing : BlockReflection.Disk Value) (padding : Value)
    (ram : Words L Value) (D B b nIn : ℕ) (hB : 0 < B) (hb : b ≤ B) :
    Represents hb (liveLogicalInput source backing ram D B b nIn)
      (livePhysicalInput source backing padding ram D B b nIn hB) := by
  refine ⟨rfl, ?_⟩
  intro j
  funext i
  by_cases hj : j.val < nIn
  · change (if j.val<nIn then _ else _) = _
    rw [if_pos hj]
    exact (expanded_representation source padding B b nIn hB hb backing ⟨j.val,hj⟩ i).symm
  · change (if j.val<nIn then _ else _) = _
    rw [if_neg hj]
    apply Eq.symm
    apply expandRun_outside
    have hm := Nat.mul_le_mul_right B (Nat.le_of_not_gt hj)
    omega

/-- Full scratch capacity D is independent of the live input/output sizes.
Only their prefixes are converted. The Policy may access all D blocks. -/
theorem simulation_live_layout (source backing target : BlockReflection.Disk Value)
    (padding : Value) (ram : Words L Value) (D B b nIn nOut : ℕ)
    (hB : 0 < B) (hb : b ≤ B) (hout : nOut ≤ D)
    (policy : Policy L b D Value) (fuel : ℕ) :
    let logical := runLogical policy fuel (liveLogicalInput source backing ram D B b nIn)
    let physical := runPhysical hb padding policy fuel
      (livePhysicalInput source backing padding ram D B b nIn hB)
    let restored := compactRun (flattenBlocks D B hB padding physical.1.disk)
      B b hB hb nOut ⟨target,[]⟩
    (∀ j : Fin nOut, ∀ i : Fin b,
      restored.disk (j.val*b+i.val) = logical.1.disk (j.castLE hout) i) ∧
    (expandRun source padding B b hB nIn ⟨backing,[]⟩).trace.length +
      physical.2 + restored.trace.length = logical.2 + 3*nIn + 5*nOut := by
  try dsimp
  have href := run_represents_and_cost hb padding policy fuel
    (liveLogicalInput source backing ram D B b nIn)
    (livePhysicalInput source backing padding ram D B b nIn hB)
    (liveInput_represents source backing padding ram D B b nIn hB hb)
  constructor
  · intro j i
    rw [compactRun_correct _ B b nOut hB hb _ j.val j.isLt i]
    have he := flattenBlocks_at D B hB padding
      (runPhysical hb padding policy fuel
        (livePhysicalInput source backing padding ram D B b nIn hB)).1.disk
      (j.castLE hout) (i.castLE hb)
    change flattenBlocks D B hB padding _ (j.val*B+i.val) = _ at he
    rw [he]
    exact (congrFun (href.1.2 (j.castLE hout)) i).symm
  · rw [expandRun_cost, compactRun_cost, ← href.2]
    simp only [List.length_nil, Nat.zero_add]
    omega

def scale (R : ℕ) := 4 * R
def threshold (R C control : ℕ) := max 8 (max (4*R) (max (4*C) (4*control)))

theorem threshold_bounds (R C control M : ℕ) (hM : threshold R C control ≤ M) :
    8 ≤ M ∧ 4*R ≤ M ∧ 4*C ≤ M ∧ 4*control ≤ M := by
  unfold threshold at hM
  omega

/-- Explicit constants independent of input size and physical memory. -/
theorem normalized_parameters (R C control M B : ℕ) (hR : 2 ≤ R)
    (hB : 0 < B) (hMB : 2*B ≤ M) (hM : threshold R C control ≤ M) :
    C ≤ M/4 ∧ R*logicalBlockSize B (scale R) ≤ M/4 ∧
    0 < logicalBlockSize B (scale R) ∧ logicalBlockSize B (scale R) ≤ B ∧
    M/4+B+control ≤ M ∧
    (∀ blocks, blocks*B ≤ (2*scale R)*(blocks*logicalBlockSize B (scale R))) ∧
    Real.log ((M : ℝ)/(B : ℝ))/4 ≤
      Real.log (((M/4 : ℕ) : ℝ)/(logicalBlockSize B (scale R) : ℝ)) ∧
    Real.log (((M/4 : ℕ) : ℝ)/(logicalBlockSize B (scale R) : ℝ)) ≤
      (1+Real.log (2*scale R : ℝ)/Real.log 2)*Real.log ((M : ℝ)/(B : ℝ)) ∧
    Real.log (M : ℝ)/4 ≤ Real.log ((M/4 : ℕ) : ℝ) ∧
      Real.log ((M/4 : ℕ) : ℝ) ≤ Real.log (M : ℝ) := by
  obtain ⟨h8, hR4, hC4, hc4⟩ := threshold_bounds R C control M hM
  have hK : 8 ≤ scale R := by unfold scale; omega
  have hratio := normalized_log_ratio M B (scale R) h8 hK hB hMB
  have hmemory := normalized_log_memory M h8
  refine ⟨by omega, normalized_ratio M B R (scale R) (le_refl _) hR4 (by omega),
    logical_block_positive B (scale R), logical_block_le_physical B (scale R) hB,
    physical_memory_budget M B control hMB hc4, ?_,
    hratio.1, hratio.2, hmemory.1, hmemory.2⟩
  intro blocks
  exact disk_space_expansion blocks B (scale R) (by omega)

/-- Conversion is a real sequence of physical reads and writes. The two
directions together cost at most 16K ceil(L/B); scratch plus the transfer
buffer fits in the same reserved memory as the simulator. -/
theorem normalization_layout {Value : Type*} (source target₁ target₂ : BlockReflection.Disk Value)
    (padding : Value) (R C control M B L : ℕ) (hR : 2 ≤ R)
    (hB : 0 < B) (hMB : 2*B ≤ M) (hM : threshold R C control ≤ M) :
    let K := scale R
    let b := logicalBlockSize B K
    let n := blockCount L b
    let expanded := expandRun source padding B b hB n ⟨target₁, []⟩
    let compacted := compactRun expanded.disk B b hB (logical_block_le_physical B K hB)
      n ⟨target₂, []⟩
    (∀ y : Fin L, compacted.disk y.val = source y.val) ∧
      expanded.trace.length + compacted.trace.length ≤ 16*K*blockCount L B ∧
      b+B+control ≤ M := by
  try dsimp
  have hK : 0 < scale R := by unfold scale; omega
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact roundtrip_prefix source padding target₁ target₂ L B _ hB
      (logical_block_positive B (scale R)) (logical_block_le_physical B (scale R) hB) y
  · have he := normalized_expand_cost source padding L B (scale R) hB hK target₁
    have hc := normalized_compact_cost
      (expandRun source padding B (logicalBlockSize B (scale R)) hB
        (blockCount L (logicalBlockSize B (scale R))) ⟨target₁, []⟩).disk
      L B (scale R) hB hK target₂
    nlinarith only [he, hc]
  · obtain ⟨h8, hR4, hC4, hc4⟩ := threshold_bounds R C control M hM
    apply conversion_memory M B _ control ?_ hMB hc4
    have h := normalized_ratio M B R (scale R) (le_refl _) hR4 (by omega)
    have hb := logical_block_positive B (scale R)
    nlinarith only [h, hR, Nat.zero_le (logicalBlockSize B (scale R))]

end CSL.NormalizationComplete
end NormalizationComplete


