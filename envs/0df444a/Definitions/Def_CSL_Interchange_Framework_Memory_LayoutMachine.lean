-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Memory_LayoutMachine
-- name    : CSL_Interchange_Framework_Memory_LayoutMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:32:31.562814+00:00
-- url     : https://prove2.me/theorems/c5459063-b07f-40c8-8973-5cb2a3201d46
-- title:
--   Coded sorting library: Interchange / Framework / Memory / LayoutMachine
-- statement:
--   Module `CodedSorting.Interchange.Framework.Memory.LayoutMachine` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Reversing fixed-length segments by physical block reads
--
--   Addresses are public counters. Only values are stored on disk and in the
--   buffers. The source and target files are distinct. The construction reads
--   four source blocks and writes one output block, independently of the segment
--   length, including the case where many short segments meet one block.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Memory.LayoutMachine

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_TapeMachine
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Definitions.Def_CSL_Shared_Programs_Normalization

section BlockReflection
/-!
# Reversing fixed-length segments by physical block reads

Addresses are public counters. Only values are stored on disk and in the
buffers. The source and target files are distinct. The construction reads
four source blocks and writes one output block, independently of the segment
length, including the case where many short segments meet one block.
-/

namespace CSL.BlockReflection

def reverseAddress (L x : ℕ) : ℕ := L * (x / L) + (L - 1 - x % L)

def segmentReverseEquiv (T L : ℕ) : Equiv.Perm (Fin (T * L)) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin T)) (Fin.revPerm : Equiv.Perm (Fin L))).trans
      finProdFinEquiv)

@[simp] theorem segmentReverse_pair (T L : ℕ) (p : Fin T) (i : Fin L) :
    segmentReverseEquiv T L (finProdFinEquiv (p, i)) =
      finProdFinEquiv (p, i.rev) := by
  simp [segmentReverseEquiv]

theorem segmentReverse_val (T L : ℕ) (x : Fin (T * L)) :
    (segmentReverseEquiv T L x).val = reverseAddress L x.val := by
  change (x.modNat.rev).val + L * (x.divNat).val = _
  simp [Fin.val_rev, Fin.coe_modNat, Fin.coe_divNat, reverseAddress, Nat.add_comm]
  omega

theorem segmentReverse_involutive (T L : ℕ) :
    Function.Involutive (segmentReverseEquiv T L) := by
  intro x
  obtain ⟨⟨p, i⟩, rfl⟩ := finProdFinEquiv.surjective x
  simp

theorem reverseAddress_balance (L x : ℕ) (hL : 0 < L) :
    reverseAddress L x + x + 1 = (2 * (x / L) + 1) * L := by
  have hmod := Nat.mod_lt x hL
  have heq := Nat.mod_add_div x L
  unfold reverseAddress
  have hsub : L - 1 - x % L + x % L + 1 = L := by omega
  nlinarith

theorem reverseAddress_near (L x : ℕ) (hL : 0 < L) :
    reverseAddress L x < x + L ∧ x < reverseAddress L x + L := by
  have hmod := Nat.mod_lt x hL
  have heq := Nat.mod_add_div x L
  unfold reverseAddress
  constructor <;> omega

private theorem one_step_cases (a b : ℕ) (h : a ≤ b) (h' : b ≤ a + 1) :
    a = b ∨ a = b - 1 := by omega

private theorem three_step_cases (a b : ℕ) (h : b ≤ a + 1) (h' : a ≤ b + 1) :
    a = b - 1 ∨ a = b ∨ a = b + 1 := by omega

theorem nearby_block (B u v : ℕ) (hB : 0 < B)
    (huv : u ≤ v) (hvu : v < u + B) :
    u / B = v / B ∨ u / B = v / B - 1 := by
  have hu := Nat.mod_lt u hB
  have hv := Nat.mod_lt v hB
  have heu := Nat.mod_add_div u B
  have hev := Nat.mod_add_div v B
  have hle : u / B ≤ v / B := Nat.div_le_div_right huv
  have hbound : v / B ≤ u / B + 1 := by
    by_contra h
    have hi : u / B + 2 ≤ v / B := by omega
    have hm := Nat.mul_le_mul_left B hi
    nlinarith only [hm, heu, hev, hu, hvu, Nat.zero_le (v % B)]
  exact one_step_cases _ _ hle hbound

def center (L x j : ℕ) : ℕ := (2 * j + 1) * L - 1 - x

/-- Four public source block numbers; repetitions cause harmless extra reads. -/
def sourceBlock (B L b : ℕ) (slot : Fin 4) : ℕ :=
  if L ≤ B then
    if slot.val = 0 then b - 1 else if slot.val = 1 then b else b + 1
  else
    let c := center L (b * B) (b * B / L + slot.val / 2)
    if slot.val % 2 = 0 then c / B else c / B - 1

theorem short_source_block (B L b y : ℕ) (hB : 0 < B) (hL : 0 < L)
    (hLB : L ≤ B) (hy0 : b * B ≤ y) (hy1 : y < (b + 1) * B) :
    reverseAddress L y / B = b - 1 ∨ reverseAddress L y / B = b ∨
      reverseAddress L y / B = b + 1 := by
  have hn := reverseAddress_near L y hL
  let u := reverseAddress L y
  change u < y + L ∧ y < u + L at hn
  change u / B = b - 1 ∨ u / B = b ∨ u / B = b + 1
  have hm := Nat.mod_lt u hB
  have he := Nat.mod_add_div u B
  have hlo : b ≤ u / B + 1 := by
    by_contra hh
    have hi : u / B + 2 ≤ b := by omega
    have hp := Nat.mul_le_mul_left B hi
    nlinarith [hn.2]
  have hhi : u / B ≤ b + 1 := by
    by_contra hh
    have hi : b + 2 ≤ u / B := by omega
    have hp := Nat.mul_le_mul_left B hi
    nlinarith only [hp, he, hy1, hn.1, hLB, Nat.zero_le (u % B)]
  exact three_step_cases _ _ hlo hhi

theorem long_source_block (B L b y : ℕ) (hB : 0 < B) (hBL : B < L)
    (hy0 : b * B ≤ y) (hy1 : y < (b + 1) * B) :
    ∃ j : Fin 2, reverseAddress L y / B = center L (b * B) (b * B / L + j.val) / B ∨
      reverseAddress L y / B = center L (b * B) (b * B / L + j.val) / B - 1 := by
  have hL : 0 < L := by omega
  have hnext : y < b * B + L := by nlinarith
  have hb := nearby_block L (b * B) y hL hy0 hnext
  have hj : y / L = b * B / L ∨ y / L = b * B / L + 1 := by
    have hle : b * B / L ≤ y / L := Nat.div_le_div_right hy0
    omega
  have hbalance := reverseAddress_balance L y hL
  have hcenter : center L (b * B) (y / L) = reverseAddress L y + (y - b * B) := by
    unfold center
    omega
  have hwindow : center L (b * B) (y / L) < reverseAddress L y + B := by
    rw [hcenter]
    have hy1' : y < b * B + B := by nlinarith
    omega
  have hu : reverseAddress L y ≤ center L (b * B) (y / L) := by omega
  have hblocks := nearby_block B (reverseAddress L y) (center L (b * B) (y / L))
    hB hu hwindow
  rcases hj with hj | hj
  · refine ⟨0, ?_⟩
    simpa [hj] using hblocks
  · refine ⟨1, ?_⟩
    simpa [hj] using hblocks

theorem sourceBlock_covers (B L b y : ℕ) (hB : 0 < B) (hL : 0 < L)
    (hy0 : b * B ≤ y) (hy1 : y < (b + 1) * B) :
    ∃ slot : Fin 4, sourceBlock B L b slot = reverseAddress L y / B := by
  by_cases hLB : L ≤ B
  · rcases short_source_block B L b y hB hL hLB hy0 hy1 with h | h | h
    · exact ⟨0, by simpa [sourceBlock, hLB] using h.symm⟩
    · exact ⟨1, by simpa [sourceBlock, hLB] using h.symm⟩
    · exact ⟨2, by simpa [sourceBlock, hLB] using h.symm⟩
  · obtain ⟨j, hj⟩ := long_source_block B L b y hB (by omega) hy0 hy1
    fin_cases j <;> rcases hj with hj | hj
    · exact ⟨0, by simpa [sourceBlock, hLB] using hj.symm⟩
    · exact ⟨1, by simpa [sourceBlock, hLB] using hj.symm⟩
    · exact ⟨2, by simpa [sourceBlock, hLB] using hj.symm⟩
    · exact ⟨3, by simpa [sourceBlock, hLB] using hj.symm⟩

def sourceSlot (B L b y : ℕ) : Fin 4 :=
  if sourceBlock B L b 0 = reverseAddress L y / B then 0
  else if sourceBlock B L b 1 = reverseAddress L y / B then 1
  else if sourceBlock B L b 2 = reverseAddress L y / B then 2 else 3

theorem sourceSlot_correct (B L b y : ℕ) (hB : 0 < B) (hL : 0 < L)
    (hy0 : b * B ≤ y) (hy1 : y < (b + 1) * B) :
    sourceBlock B L b (sourceSlot B L b y) = reverseAddress L y / B := by
  obtain ⟨slot, hs⟩ := sourceBlock_covers B L b y hB hL hy0 hy1
  unfold sourceSlot
  split_ifs with h0 h1 h2
  · exact h0
  · exact h1
  · exact h2
  · fin_cases slot <;> simp_all

variable {Value : Type*}

abbrev Disk (Value : Type*) := ℕ → Value

/-- One ordinary aligned physical block read. -/
def readBlock (source : Disk Value) (B block : ℕ) : Fin B → Value :=
  fun i => source (block * B + i.val)

/-- Exactly four physical block reads, chosen only from public addresses. -/
def loadFour (source : Disk Value) (B L b : ℕ) : Fin 4 → Fin B → Value :=
  fun slot => readBlock source B (sourceBlock B L b slot)

/-- This stage accesses the four resident blocks, not the external source. -/
def assemble (B L b : ℕ) (hB : 0 < B) (cache : Fin 4 → Fin B → Value) : Fin B → Value :=
  fun i => cache (sourceSlot B L b (b * B + i.val))
    ⟨reverseAddress L (b * B + i.val) % B, Nat.mod_lt _ hB⟩

theorem assembled_correct (source : Disk Value) (B L b : ℕ)
    (hB : 0 < B) (hL : 0 < L) (i : Fin B) :
    assemble B L b hB (loadFour source B L b) i =
      source (reverseAddress L (b * B + i.val)) := by
  unfold assemble loadFour readBlock
  rw [sourceSlot_correct B L b _ hB hL (by omega) (by nlinarith [i.isLt])]
  congr 1
  simpa only [Nat.mul_comm] using Nat.div_add_mod (reverseAddress L (b * B + i.val)) B

/-- One aligned block write to a separate target file. -/
def writeBlock (target : Disk Value) (B b : ℕ) (hB : 0 < B)
    (buffer : Fin B → Value) : Disk Value := fun y =>
  if y / B = b then buffer ⟨y % B, Nat.mod_lt _ hB⟩ else target y

inductive Transfer where
  | read (block : ℕ)
  | write (block : ℕ)
  deriving DecidableEq

structure Execution (Value : Type*) where
  disk : Disk Value
  trace : List Transfer

/-- One execution step has four reads, local assembly, and one write. -/
def step (source : Disk Value) (B L b : ℕ) (hB : 0 < B)
    (state : Execution Value) : Execution Value :=
  let cache := loadFour source B L b
  let output := assemble B L b hB cache
  ⟨writeBlock state.disk B b hB output,
    state.trace ++ [Transfer.read (sourceBlock B L b 0),
      Transfer.read (sourceBlock B L b 1), Transfer.read (sourceBlock B L b 2),
      Transfer.read (sourceBlock B L b 3), Transfer.write b]⟩

def run (source : Disk Value) (B L : ℕ) (hB : 0 < B) :
    ℕ → Execution Value → Execution Value
  | 0, state => state
  | n + 1, state => step source B L n hB (run source B L hB n state)

theorem run_transfers (source : Disk Value) (B L : ℕ) (hB : 0 < B)
    (n : ℕ) (state : Execution Value) :
    (run source B L hB n state).trace.length = state.trace.length + 5 * n := by
  induction n with
  | zero => simp [run]
  | succ n ih => simp [run, step, ih, Nat.mul_add, Nat.add_assoc]

theorem run_prefix (source : Disk Value) (B L : ℕ) (hB : 0 < B) (hL : 0 < L)
    (n : ℕ) (state : Execution Value) (y : ℕ) (hy : y < n * B) :
    (run source B L hB n state).disk y = source (reverseAddress L y) := by
  induction n with
  | zero => simp at hy
  | succ n ih =>
    change (if y / B = n then _ else _) = _
    split_ifs with h
    · have hc := assembled_correct source B L n hB hL ⟨y % B, Nat.mod_lt _ hB⟩
      have he : n * B + y % B = y := by
        rw [← h]
        simpa only [Nat.mul_comm] using Nat.div_add_mod y B
      simpa only [he] using hc
    · apply ih
      have hydiv : y / B < n + 1 := (Nat.div_lt_iff_lt_mul hB).2 hy
      have hydiv' : y / B < n := by omega
      exact (Nat.div_lt_iff_lt_mul hB).1 hydiv'

theorem run_outside (source : Disk Value) (B L : ℕ) (hB : 0 < B)
    (n : ℕ) (state : Execution Value) (y : ℕ) (hy : n * B ≤ y) :
    (run source B L hB n state).disk y = state.disk y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hdiv : n + 1 ≤ y / B := (Nat.le_div_iff_mul_le hB).2 hy
    change (if y / B = n then _ else _) = _
    rw [if_neg (by omega)]
    apply ih
    nlinarith

/-- The resident payload consists of four input blocks and one output block.
The disk functions and trace are external storage / specification history. -/
abbrev Resident (B : ℕ) (Value : Type*) := (Fin 4 → Fin B → Value) × (Fin B → Value)

theorem resident_cell_count (B : ℕ) :
    Fintype.card ((Fin 4 × Fin B) ⊕ Fin B) = 5 * B := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

theorem full_reversal (source : Disk Value) (target : Disk Value)
    (B T L : ℕ) (hB : 0 < B) (hL : 0 < L) :
    let n := (T * L + B - 1) / B
    let result := run source B L hB n ⟨target, []⟩
    (∀ y : Fin (T * L), result.disk y.val = source (segmentReverseEquiv T L y).val) ∧
      result.trace.length = 5 * n := by
  try dsimp
  constructor
  · intro y
    rw [segmentReverse_val]
    apply run_prefix source B L hB hL
    have he := Nat.mod_add_div (T * L + B - 1) B
    have hm := Nat.mod_lt (T * L + B - 1) hB
    have hn' : T * L ≤ B * ((T * L + B - 1) / B) := by omega
    have hn : T * L ≤ ((T * L + B - 1) / B) * B := by
      simpa only [Nat.mul_comm] using hn'
    exact lt_of_lt_of_le y.isLt hn
  · simpa using run_transfers source B L hB ((T * L + B - 1) / B) ⟨target, []⟩

/-- Unwritten disk space and padding beyond the valid input may contain
arbitrary values. They cannot affect any valid output of the block program. -/
theorem full_reversal_congr (source₁ source₂ target₁ target₂ : Disk Value)
    (B T L : ℕ) (hB : 0 < B) (hL : 0 < L)
    (hsource : ∀ y : Fin (T*L), source₁ y.val = source₂ y.val) (y : Fin (T*L)) :
    (run source₁ B L hB ((T*L+B-1)/B) ⟨target₁,[]⟩).disk y.val =
      (run source₂ B L hB ((T*L+B-1)/B) ⟨target₂,[]⟩).disk y.val := by
  rw [(full_reversal source₁ target₁ B T L hB hL).1 y,
    (full_reversal source₂ target₂ B T L hB hL).1 y]
  exact hsource (segmentReverseEquiv T L y)

end CSL.BlockReflection
end BlockReflection

section LayoutConversion
/-! Compact-to-dedicated block conversion with one transfer buffer and one
logical-block scratch array. The input, output and transfer history are
external/specification objects; no address tags are stored with records. -/

namespace CSL.LayoutConversion

open BlockReflection
variable {Value : Type*}

private theorem next_cases (a b : ℕ) (hle : a ≤ b) (h : a = b ∨ a = b - 1) :
    b = a ∨ b = a + 1 := by omega

theorem two_blocks (B b start i : ℕ) (hB : 0 < B) (hb : b ≤ B) (hi : i < b) :
    (start + i) / B = start / B ∨ (start + i) / B = start / B + 1 := by
  have hn := nearby_block B start (start+i) hB (by omega) (by omega)
  have hd : start / B ≤ (start+i) / B := Nat.div_le_div_right (by omega)
  exact next_cases _ _ hd hn

/-- Copy the part of the logical block found in this physical buffer. -/
def extract (B b start block : ℕ) (hB : 0 < B)
    (buffer : Fin B → Value) (scratch : Fin b → Value) : Fin b → Value := fun i =>
  if (start+i.val) / B = block then
    buffer ⟨(start+i.val) % B, Nat.mod_lt _ hB⟩ else scratch i

def logicalRead (source : Disk Value) (padding : Value) (B b start : ℕ) (hB : 0 < B) :
    Fin b → Value :=
  let first := readBlock source B (start / B)
  let scratch := extract B b start (start / B) hB first (fun _ => padding)
  let second := readBlock source B (start / B + 1)
  extract B b start (start / B + 1) hB second scratch

theorem logicalRead_correct (source : Disk Value) (padding : Value)
    (B b start : ℕ) (hB : 0 < B) (hb : b ≤ B) (i : Fin b) :
    logicalRead source padding B b start hB i = source (start+i.val) := by
  have he : ((start+i.val) / B) * B + (start+i.val) % B = start+i.val := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod (start+i.val) B
  rcases two_blocks B b start i.val hB hb i.isLt with h | h
  · have hne : (start+i.val) / B ≠ start / B + 1 := by omega
    simp only [logicalRead, extract, if_neg hne, if_pos h, readBlock]
    rw [← h]
    simpa using congrArg source he
  · simp only [logicalRead, extract, if_pos h, readBlock]
    rw [← h]
    simpa using congrArg source he

def expandStep (source : Disk Value) (padding : Value)
    (B b j : ℕ) (hB : 0 < B) (state : Execution Value) : Execution Value :=
  let scratch := logicalRead source padding B b (j*b) hB
  let output := Normalization.pack (B := B) padding scratch
  ⟨writeBlock state.disk B j hB output,
    state.trace ++ [.read (j*b / B), .read (j*b / B + 1), .write j]⟩

def expandRun (source : Disk Value) (padding : Value) (B b : ℕ) (hB : 0 < B) :
    ℕ → Execution Value → Execution Value
  | 0, state => state
  | n+1, state => expandStep source padding B b n hB (expandRun source padding B b hB n state)

theorem expandRun_cost (source : Disk Value) (padding : Value) (B b n : ℕ)
    (hB : 0 < B) (state : Execution Value) :
    (expandRun source padding B b hB n state).trace.length = state.trace.length + 3*n := by
  induction n with
  | zero => simp [expandRun]
  | succ n ih => simp [expandRun, expandStep, ih, Nat.mul_add, Nat.add_assoc]

theorem expandRun_correct (source : Disk Value) (padding : Value) (B b n : ℕ)
    (hB : 0 < B) (hb : b ≤ B) (state : Execution Value)
    (j : ℕ) (hj : j < n) (i : Fin B) :
    (expandRun source padding B b hB n state).disk (j*B+i.val) =
      if i.val < b then source (j*b+i.val) else padding := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hdiv : (j*B+i.val) / B = j := by
      rw [Nat.mul_comm j B, Nat.mul_add_div hB, Nat.div_eq_of_lt i.isLt, Nat.add_zero]
    have hmod : (j*B+i.val) % B = i.val := by simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    change (if (j*B+i.val) / B = n then _ else _) = _
    by_cases h : j = n
    · subst j
      rw [if_pos hdiv]
      change Normalization.pack padding (logicalRead source padding B b (n*b) hB)
        ⟨(n*B+i.val)%B, _⟩ = _
      simp only [Normalization.pack, hmod]
      split_ifs with hi
      · exact logicalRead_correct source padding B b (n*b) hB hb ⟨i.val, hi⟩
      · rfl
    · rw [if_neg (by omega)]
      exact ih (by omega)

/-- Valid prefixes of the produced physical blocks represent exactly the
original compact logical blocks in the simulator's representation relation. -/
theorem expanded_representation (source : Disk Value) (padding : Value)
    (B b n : ℕ) (hB : 0 < B) (hb : b ≤ B) (target : Disk Value)
    (j : Fin n) (i : Fin b) :
    (expandRun source padding B b hB n ⟨target, []⟩).disk (j.val*B+i.val) =
      source (j.val*b+i.val) := by
  simpa only [Fin.coe_castLE, if_pos i.isLt] using
    expandRun_correct source padding B b n hB hb ⟨target, []⟩ j.val j.isLt (i.castLE hb)

/-- Conversion writes only the live input prefix, not the whole scratch disk. -/
theorem expandRun_outside (source : Disk Value) (padding : Value) (B b n : ℕ)
    (hB : 0 < B) (state : Execution Value) (y : ℕ) (hy : n*B ≤ y) :
    (expandRun source padding B b hB n state).disk y = state.disk y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hdiv : n+1 ≤ y/B := (Nat.le_div_iff_mul_le hB).2 hy
    change (if y/B=n then _ else _) = _
    rw [if_neg (by omega)]
    apply ih
    nlinarith

def blockCount (L b : ℕ) := (L+b-1)/b

theorem blockCount_covers (L b : ℕ) (hb : 0 < b) : L ≤ blockCount L b * b := by
  have h := Nat.mod_lt (L+b-1) hb
  have he := Nat.mod_add_div (L+b-1) b
  have h' : L ≤ b * ((L+b-1)/b) := by omega
  simpa only [blockCount, Nat.mul_comm] using h'

theorem blockCount_minimal (L b n : ℕ) (hb : 0 < b) (h : L ≤ n*b) :
    blockCount L b ≤ n := by
  have h' : L+b-1 < (n+1)*b := by
    calc
      L+b-1 < n*b+b := by omega
      _ = (n+1)*b := by ring
  have hd : (L+b-1)/b < n+1 := (Nat.div_lt_iff_lt_mul hb).2 h'
  exact Nat.le_of_lt_succ hd

theorem normalized_blockCount (L B K : ℕ) (hB : 0 < B) (hK : 0 < K) :
    blockCount L (Normalization.logicalBlockSize B K) ≤ 2*K*blockCount L B := by
  apply blockCount_minimal _ _ _ (Normalization.logical_block_positive B K)
  calc
    L ≤ blockCount L B * B := blockCount_covers L B hB
    _ ≤ blockCount L B * (2*K*Normalization.logicalBlockSize B K) :=
      Nat.mul_le_mul_left _ (Normalization.block_expansion_bound B K hK)
    _ = 2*K*blockCount L B*Normalization.logicalBlockSize B K := by ring

theorem normalized_expand_cost (source : Disk Value) (padding : Value)
    (L B K : ℕ) (hB : 0 < B) (hK : 0 < K) (target : Disk Value) :
    (expandRun source padding B (Normalization.logicalBlockSize B K) hB
      (blockCount L (Normalization.logicalBlockSize B K)) ⟨target, []⟩).trace.length ≤
      6*K*blockCount L B := by
  rw [expandRun_cost]
  simp only [List.length_nil, Nat.zero_add]
  nlinarith only [normalized_blockCount L B K hB hK]

def overlay {b : ℕ} (start : ℕ) (scratch : Fin b → Value) (target : Disk Value) : Disk Value :=
  fun y => if h : start ≤ y ∧ y < start+b then scratch ⟨y-start, by omega⟩ else target y

def patchBuffer (B b start block : ℕ) (scratch : Fin b → Value)
    (old : Fin B → Value) : Fin B → Value := fun i =>
  if h : start ≤ block*B+i.val ∧ block*B+i.val < start+b then
    scratch ⟨block*B+i.val-start, by omega⟩ else old i

/-- A read-modify-write of one compact target block, with the logical block
retained in scratch and the physical transfer buffer reused. -/
def patchBlock (B b start block : ℕ) (hB : 0 < B) (scratch : Fin b → Value)
    (target : Disk Value) : Disk Value :=
  writeBlock target B block hB (patchBuffer B b start block scratch (readBlock target B block))

theorem patchBlock_spec (B b start block : ℕ) (hB : 0 < B) (scratch : Fin b → Value)
    (target : Disk Value) (y : ℕ) :
    patchBlock B b start block hB scratch target y =
      if y/B=block then overlay start scratch target y else target y := by
  by_cases hdiv : y/B=block
  · have he : block*B+y%B=y := by
      rw [← hdiv]
      simpa only [Nat.mul_comm] using Nat.div_add_mod y B
    simp only [patchBlock, writeBlock, if_pos hdiv, patchBuffer, he, readBlock, overlay]
  · simp [patchBlock, writeBlock, hdiv]

theorem two_patches (B b start : ℕ) (hB : 0 < B) (hb : b ≤ B)
    (scratch : Fin b → Value) (target : Disk Value) :
    patchBlock B b start (start/B+1) hB scratch
      (patchBlock B b start (start/B) hB scratch target) = overlay start scratch target := by
  funext y
  rw [patchBlock_spec, patchBlock_spec]
  by_cases hy : start ≤ y ∧ y < start+b
  · have hn := two_blocks B b start (y-start) hB hb (by omega)
    have he : start+(y-start)=y := by omega
    rw [he] at hn
    rcases hn with hn | hn
    · have hne : y/B ≠ start/B+1 := by omega
      simp only [if_neg hne, if_pos hn, overlay, dif_pos hy]
    · simp only [if_pos hn, overlay, dif_pos hy]
  · simp only [patchBlock_spec, overlay, dif_neg hy]
    split_ifs <;> rfl

def compactStep (source : Disk Value) (B b j : ℕ) (hB : 0 < B) (hb : b ≤ B)
    (state : Execution Value) : Execution Value :=
  let buffer := readBlock source B j
  let scratch : Fin b → Value := fun i => buffer (i.castLE hb)
  let first := patchBlock B b (j*b) (j*b/B) hB scratch state.disk
  let second := patchBlock B b (j*b) (j*b/B+1) hB scratch first
  ⟨second, state.trace ++ [.read j, .read (j*b/B), .write (j*b/B),
    .read (j*b/B+1), .write (j*b/B+1)]⟩

theorem compactStep_spec (source : Disk Value) (B b j : ℕ) (hB : 0 < B) (hb : b ≤ B)
    (state : Execution Value) :
    (compactStep source B b j hB hb state).disk =
      overlay (j*b) (fun i : Fin b => source (j*B+i.val)) state.disk := by
  exact two_patches B b (j*b) hB hb _ state.disk

def compactRun (source : Disk Value) (B b : ℕ) (hB : 0 < B) (hb : b ≤ B) :
    ℕ → Execution Value → Execution Value
  | 0, state => state
  | n+1, state => compactStep source B b n hB hb (compactRun source B b hB hb n state)

theorem compactRun_cost (source : Disk Value) (B b n : ℕ) (hB : 0 < B) (hb : b ≤ B)
    (state : Execution Value) :
    (compactRun source B b hB hb n state).trace.length = state.trace.length + 5*n := by
  induction n with
  | zero => simp [compactRun]
  | succ n ih => simp [compactRun, compactStep, ih, Nat.mul_add, Nat.add_assoc]

theorem compactRun_correct (source : Disk Value) (B b n : ℕ) (hB : 0 < B) (hb : b ≤ B)
    (state : Execution Value) (j : ℕ) (hj : j < n) (i : Fin b) :
    (compactRun source B b hB hb n state).disk (j*b+i.val) = source (j*B+i.val) := by
  induction n with
  | zero => omega
  | succ n ih =>
    change (compactStep source B b n hB hb _).disk _ = _
    rw [compactStep_spec]
    by_cases h : j=n
    · subst j
      have hy : n*b ≤ n*b+i.val ∧ n*b+i.val < n*b+b := by constructor <;> omega
      simp [overlay, hy]
    · have hj' : j<n := by omega
      have he : j*b+i.val < n*b := by
        have hm := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hj')
        nlinarith only [hm, i.isLt]
      have hnot : ¬ (n*b ≤ j*b+i.val ∧ j*b+i.val < n*b+b) := by omega
      simp only [overlay, dif_neg hnot]
      exact ih hj'

theorem normalized_compact_cost (source : Disk Value)
    (L B K : ℕ) (hB : 0 < B) (hK : 0 < K) (target : Disk Value) :
    (compactRun source B (Normalization.logicalBlockSize B K) hB
      (Normalization.logical_block_le_physical B K hB)
      (blockCount L (Normalization.logicalBlockSize B K)) ⟨target, []⟩).trace.length ≤
      10*K*blockCount L B := by
  rw [compactRun_cost]
  simp only [List.length_nil, Nat.zero_add]
  nlinarith only [normalized_blockCount L B K hB hK]

theorem roundtrip (source : Disk Value) (padding : Value)
    (target₁ target₂ : Disk Value) (B b n : ℕ) (hB : 0 < B) (hb : b ≤ B)
    (j : Fin n) (i : Fin b) :
    (compactRun (expandRun source padding B b hB n ⟨target₁, []⟩).disk
      B b hB hb n ⟨target₂, []⟩).disk (j.val*b+i.val) = source (j.val*b+i.val) := by
  rw [compactRun_correct _ B b n hB hb _ j.val j.isLt i]
  exact expanded_representation source padding B b n hB hb target₁ j i

theorem roundtrip_prefix (source : Disk Value) (padding : Value)
    (target₁ target₂ : Disk Value) (L B b : ℕ) (hB : 0 < B) (hb0 : 0 < b) (hb : b ≤ B)
    (y : Fin L) :
    (compactRun (expandRun source padding B b hB (blockCount L b) ⟨target₁, []⟩).disk
      B b hB hb (blockCount L b) ⟨target₂, []⟩).disk y.val = source y.val := by
  have hn := blockCount_covers L b hb0
  have hj : y.val / b < blockCount L b :=
    (Nat.div_lt_iff_lt_mul hb0).2 (lt_of_lt_of_le y.isLt hn)
  have he : y.val / b * b + y.val % b = y.val := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod y.val b
  simpa only [he] using roundtrip source padding target₁ target₂ B b (blockCount L b)
    hB hb ⟨y.val / b, hj⟩ ⟨y.val % b, Nat.mod_lt _ hb0⟩

theorem conversion_memory (M B b control : ℕ) (hb : b ≤ M/4)
    (hMB : 2*B ≤ M) (hc : 4*control ≤ M) : b+B+control ≤ M := by
  have hm := Normalization.physical_memory_budget M B control hMB hc
  omega

theorem resident_word_count (B b : ℕ) :
    Fintype.card (Fin B ⊕ Fin b) = B+b := by simp

end CSL.LayoutConversion
end LayoutConversion

section LayoutMachine
/-! Primitive-state refinement for Appendix A's layout converters.
Every transition has exactly one B-word transfer buffer and one b-word
scratch array. A local transition cannot access either external disk. -/

namespace CSL.LayoutMachine

open BlockReflection LayoutConversion
variable {Value : Type*} {B b : ℕ}

structure RAM (B b : ℕ) (Value : Type*) where
  buffer : Fin B → Value
  scratch : Fin b → Value

structure State (B b : ℕ) (Value : Type*) where
  ram : RAM B b Value
  output : Disk Value
  trace : List Transfer

inductive Command where
  | sourceRead (block : ℕ)
  | targetRead (block : ℕ)
  | clearScratch
  | extract (start block : ℕ)
  | copyPrefix
  | pack
  | patch (start block : ℕ)
  | write (block : ℕ)

def primitive (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B)
    (cmd : Command) (s : State B b Value) : State B b Value :=
  match cmd with
  | .sourceRead block =>
      ⟨⟨readBlock source B block,s.ram.scratch⟩,s.output,s.trace ++ [.read block]⟩
  | .targetRead block =>
      ⟨⟨readBlock s.output B block,s.ram.scratch⟩,s.output,s.trace ++ [.read block]⟩
  | .clearScratch => ⟨⟨s.ram.buffer,fun _ => padding⟩,s.output,s.trace⟩
  | .extract start block =>
      ⟨⟨s.ram.buffer,LayoutConversion.extract B b start block hB s.ram.buffer s.ram.scratch⟩,
        s.output,s.trace⟩
  | .copyPrefix => ⟨⟨s.ram.buffer,fun i => s.ram.buffer (i.castLE hb)⟩,s.output,s.trace⟩
  | .pack => ⟨⟨Normalization.pack padding s.ram.scratch,s.ram.scratch⟩,s.output,s.trace⟩
  | .patch start block =>
      ⟨⟨patchBuffer B b start block s.ram.scratch s.ram.buffer,s.ram.scratch⟩,s.output,s.trace⟩
  | .write block =>
      ⟨s.ram,writeBlock s.output B block hB s.ram.buffer,s.trace ++ [.write block]⟩

def run (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B) :
    List Command → State B b Value → State B b Value
  | [],s => s
  | cmd::rest,s => run source padding hB hb rest (primitive source padding hB hb cmd s)

def expandProgram (B b j : ℕ) : List Command :=
  [.clearScratch, .sourceRead (j*b/B), .extract (j*b) (j*b/B),
    .sourceRead (j*b/B+1), .extract (j*b) (j*b/B+1), .pack, .write j]

def compactProgram (B b j : ℕ) : List Command :=
  [.sourceRead j, .copyPrefix, .targetRead (j*b/B), .patch (j*b) (j*b/B),
    .write (j*b/B), .targetRead (j*b/B+1), .patch (j*b) (j*b/B+1), .write (j*b/B+1)]

def observe (s : State B b Value) : Execution Value := ⟨s.output,s.trace⟩

theorem expand_refines (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B)
    (j : ℕ) (s : State B b Value) :
    observe (run source padding hB hb (expandProgram B b j) s) =
      expandStep source padding B b j hB (observe s) := by
  simp only [observe, run, expandProgram, primitive, expandStep, logicalRead,
    List.append_assoc, List.singleton_append]
  rfl

theorem compact_refines (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B)
    (j : ℕ) (s : State B b Value) :
    observe (run source padding hB hb (compactProgram B b j) s) =
      compactStep source B b j hB hb (observe s) := by
  simp only [observe, run, compactProgram, primitive, compactStep, patchBlock,
    List.append_assoc, List.singleton_append]
  rfl

def expandLoop (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B) :
    ℕ → State B b Value → State B b Value
  | 0,s => s
  | n+1,s => run source padding hB hb (expandProgram B b n) (expandLoop source padding hB hb n s)

def compactLoop (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B) :
    ℕ → State B b Value → State B b Value
  | 0,s => s
  | n+1,s => run source padding hB hb (compactProgram B b n) (compactLoop source padding hB hb n s)

theorem expandLoop_refines (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B)
    (n : ℕ) (s : State B b Value) :
    observe (expandLoop source padding hB hb n s) =
      expandRun source padding B b hB n (observe s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [expandLoop, expand_refines, ih, expandRun]

theorem compactLoop_refines (source : Disk Value) (padding : Value) (hB : 0 < B) (hb : b ≤ B)
    (n : ℕ) (s : State B b Value) :
    observe (compactLoop source padding hB hb n s) =
      compactRun source B b hB hb n (observe s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [compactLoop, compact_refines, ih, compactRun]

/-- This fixed type is shared by every intermediate primitive state; the
output disk and proof history are not counted as resident arrays. -/
theorem ram_word_count : Fintype.card (Fin B ⊕ Fin b) = B+b := by simp

end CSL.LayoutMachine
end LayoutMachine


