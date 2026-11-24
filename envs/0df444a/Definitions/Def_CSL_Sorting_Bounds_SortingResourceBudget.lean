-- Prove2me | Definitions.Def_CSL_Sorting_Bounds_SortingResourceBudget
-- name    : CSL_Sorting_Bounds_SortingResourceBudget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:45:11.014739+00:00
-- url     : https://prove2.me/theorems/9c5b0e8b-1397-4168-8bdc-dbeed4e431b4
-- title:
--   Coded sorting library: Sorting / Bounds / SortingResourceBudget
-- statement:
--   Module `CodedSorting.Sorting.Bounds.SortingResourceBudget` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   One fixed reserve constant for the actual normalization controller,
--   three-word sorting records, three complete file directories, three live call
--   frames, and addressed stream residents. The lemmas certify the resident
--   layout instantiated below and its numerical capacity bounds. Execution
--   on this layout is handled by the sorting implementation modules.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Bounds.SortingResourceBudget

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_NormalizationController
import Definitions.Def_CSL_Shared_Words_WordConvention
import Definitions.Def_CSL_Shared_Records_KeyRecordWords

/-! One fixed reserve constant for the actual normalization controller,
three-word sorting records, three complete file directories, three live call
frames, and addressed stream residents. The lemmas certify the resident
layout instantiated below and its numerical capacity bounds. Execution
on this layout is handled by the sorting implementation modules. -/
set_option autoImplicit false
namespace CSL.SortingResourceBudget

/-- Readers/writers count simultaneously live normalized stream states.
`pc` is the fixed number of words for one frame's finite control code. -/
structure Inventory where
  readers : ℕ
  writers : ℕ
  keys : ℕ
  pc : ℕ
  ratio : ℕ

def digits (c exponent : ℕ) : ℕ := c*(exponent+1)
def payloadCoefficient (v : Inventory) : ℕ := 1537+v.readers+v.writers
/-- Three directories, three 13-coordinate shape descriptors and one stack-top
counter plus the leaf-length header. Pending lengths and the refill descriptor
use d words each; no block size is silently assumed to fit one word. -/
def metadata (v : Inventory) (d : ℕ) : ℕ :=
  (4*v.readers+3*v.writers+6*v.keys+42)*d+1+3*v.pc

def reserve (v : Inventory) (c d : ℕ) : ℕ :=
  16*(payloadCoefficient v+metadata v d+(4*d+3)+v.ratio+2^(3*c)+1)
def H (v : Inventory) (c d M : ℕ) : ℕ := M/reserve v c d
def block (v : Inventory) (c d B : ℕ) : ℕ :=
  Normalization.logicalBlockSize B ((reserve v c d)^2)

def sourceWords (v : Inventory) (H b d : ℕ) : ℕ :=
  1536*H+(v.readers+v.writers+1)*b+metadata v d

theorem reserve_pos (v : Inventory) (c d : ℕ) : 0 < reserve v c d := by
  have hp : 0 < 2^(3*c) := by positivity
  unfold reserve
  omega

theorem reserve_bounds (v : Inventory) (c d : ℕ) :
    16*payloadCoefficient v ≤ reserve v c d ∧
    16*metadata v d ≤ reserve v c d ∧
    16*(4*d+3) ≤ reserve v c d ∧
    v.ratio ≤ reserve v c d ∧ 2^(3*c) ≤ reserve v c d ∧ 16 ≤ reserve v c d := by
  have hp : 0 < 2^(3*c) := by positivity
  unfold reserve
  omega

theorem normalized_shape (v : Inventory) (c d M B : ℕ)
    (hM : (reserve v c d)^2 ≤ M) (hB : B ≤ M) :
    0 < H v c d M ∧ block v c d B ≤ H v c d M ∧
    v.ratio*block v c d B ≤ H v c d M := by
  let C := reserve v c d
  have hC : 0 < C := reserve_pos v c d
  have hCM : C ≤ M := by have := reserve_bounds v c d; dsimp [C]; nlinarith
  have hH : 0 < M/C := Nat.div_pos hCM hC
  have hcb : C*Normalization.logicalBlockSize B (C^2) ≤ M/C := by
    apply (Nat.le_div_iff_mul_le hC).2
    by_cases hb : 1 ≤ B/(C^2)
    · rw [Normalization.logicalBlockSize,max_eq_right hb]
      have hd := Nat.div_mul_le_self B (C^2)
      nlinarith
    · rw [Normalization.logicalBlockSize,max_eq_left (by omega)]
      simpa only [Nat.mul_one,pow_two] using hM
  refine ⟨hH,?_,?_⟩
  · exact (Nat.le_mul_of_pos_left _ hC).trans hcb
  · have hr : v.ratio ≤ C := (reserve_bounds v c d).2.2.2.1
    exact (Nat.mul_le_mul_right _ hr).trans hcb

theorem resident_bound (v : Inventory) (c d M B : ℕ)
    (hM : (reserve v c d)^2 ≤ M) (hB : 2*B ≤ M) :
    let h := H v c d M
    let b := block v c d B
    sourceWords v h b d+B+b+4*d+3 ≤ M ∧ sourceWords v h b d ≤ M/4 := by
  try dsimp only
  let C := reserve v c d
  let h := H v c d M
  let b := block v c d B
  have hbH : b ≤ h := (normalized_shape v c d M B hM (by omega)).2.1
  have bounds := reserve_bounds v c d
  have hC : 0 < C := reserve_pos v c d
  have hCM : C ≤ M := by dsimp [C]; nlinarith [bounds.2.2.2.2.2]
  have hhC : h*C ≤ M := Nat.div_mul_le_self M C
  have hleaf : 16*(payloadCoefficient v*h) ≤ M := by
    have hh := Nat.mul_le_mul_right h bounds.1
    nlinarith
  have hmeta : 16*metadata v d ≤ M := bounds.2.1.trans hCM
  have hcontrol : 16*(4*d+3) ≤ M := bounds.2.2.1.trans hCM
  have hsource : sourceWords v h b d ≤ payloadCoefficient v*h+metadata v d := by
    have hbmul := Nat.mul_le_mul_left (v.readers+v.writers+1) hbH
    unfold sourceWords payloadCoefficient
    nlinarith
  have h8source : 8*sourceWords v h b d ≤ M := by omega
  have h16h : 16*h ≤ M := by
    have hh := Nat.mul_le_mul_right h bounds.2.2.2.2.2
    nlinarith
  constructor <;> change _
  · change sourceWords v h b d+B+b+4*d+3 ≤ M
    omega
  · change sourceWords v h b d ≤ M/4
    omega

/-- Sufficiently large input under any fixed w=Omega(log N) convention
provides the same original words for the finite phase codes and record tags. -/
theorem phase_width (N w c : ℕ) (hc : 0 < c)
    (hN : 2^(3*c) ≤ N) (hw : WordConvention.Covers N w c) : 3 ≤ w := by
  have hh := Nat.clog_mono_right 2 hN
  rw [Nat.clog_pow 2 (3*c) (by decide)] at hh
  unfold WordConvention.Covers at hw
  nlinarith

theorem large_instance_width (v : Inventory) (c d M N w : ℕ) (hN : 2 ≤ N)
    (hMN : M ≤ N) (hM : (reserve v c d)^2 ≤ M)
    (hw : WordConvention.Covers N w c) : 3 ≤ w := by
  have hc := (WordConvention.positive_words N w c hN hw).2
  have hCM : reserve v c d ≤ M := by have := reserve_bounds v c d; nlinarith
  apply phase_width N w c hc _ hw
  exact ((reserve_bounds v c d).2.2.2.2.1.trans hCM).trans hMN

/-- The complete common disk has three disjoint banks of N^e blocks.
One additional fixed exponent absorbs the bank count with no change to w. -/
theorem common_disk_polynomial (N exponent : ℕ) (hN : 2 ≤ N) :
    N^exponent+(N^exponent+N^exponent) ≤ N^(exponent+2) := by
  have hsq : 3 ≤ N^2 := by nlinarith
  rw [pow_add]
  have hm := Nat.mul_le_mul_left (N^exponent) hsq
  nlinarith

end CSL.SortingResourceBudget


