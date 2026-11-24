-- Prove2me | Definitions.Def_CSLB_NormalBridge
-- name    : CSLB_NormalBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T16:14:38.837131+00:00
-- url     : https://prove2.me/theorems/f375cdde-c912-4bf6-b44f-4da16ece40cc
-- title:
--   Coded sorting bridge: NormalBridge
-- statement:
--   # The normalization controller on the external-memory machine
--
--   The resident part of a controller state (transfer buffer, RAM, scratch, counters, phase,
--   stage) and the micro-step counter are stored in the `M` machine words, transfer buffer first.
--   The program decodes its memory, performs one controller micro-step (`micro`), and issues the
--   micro-step's block transfer. Controller disk address `.inl a` (input region) and `.inr (.inr a)`
--   (output region) both live in machine block `a`; the working region `.inr (.inl a)` lives in
--   block `R + a`. The input region is only read during the input stage, before any output block is
--   written, so the two regions may share their blocks.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CodedSorting_Machine
import Definitions.Def_CSLB_ControllerMicro

/-! # The normalization controller on the external-memory machine

The resident part of a controller state (transfer buffer, RAM, scratch, counters, phase,
stage) and the micro-step counter are stored in the `M` machine words, transfer buffer first.
The program decodes its memory, performs one controller micro-step (`micro`), and issues the
micro-step's block transfer. Controller disk address `.inl a` (input region) and `.inr (.inr a)`
(output region) both live in machine block `a`; the working region `.inr (.inl a)` lives in
block `R + a`. The input region is only read during the input stage, before any output block is
written, so the two regions may share their blocks. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CSLB.NormalBridge
open CodedSorting CSLB.MicroSpecs CSLB.ControllerMicro

variable {L R B b d w M : ℕ}

local instance {α : Type*} (o : Option α) : Decidable (o=none) := Option.decidable_eq_none o

/-- The memory size used by the encoding. -/
def need (L B b d : ℕ) : ℕ := B + L + b + 3 * d + 3

/-- Machine memory holding the resident state `s` and the micro-step counter `r`. -/
def enc (hM : need L B b d ≤ M) (s : CSL.CommonNormalizationController.State L R B b d w)
    (r : Word w) : Mem M w := fun j =>
  if h1 : j.val < B then s.buffer ⟨j.val, h1⟩
  else if h2 : j.val < B + L then s.ram ⟨j.val - B, by omega⟩
  else if h3 : j.val < B + L + b then s.scratch ⟨j.val - (B + L), by omega⟩
  else if h4 : j.val < B + L + b + d then s.counter ⟨j.val - (B + L + b), by omega⟩
  else if h5 : j.val < B + L + b + 2 * d then s.inputCount ⟨j.val - (B + L + b + d), by omega⟩
  else if h6 : j.val < B + L + b + 3 * d then s.outputCount ⟨j.val - (B + L + b + 2 * d), by omega⟩
  else if j.val = B + L + b + 3 * d then s.phase
  else if j.val = B + L + b + 3 * d + 1 then s.stage
  else if j.val = B + L + b + 3 * d + 2 then r
  else 0

/-- Read back the resident state (with disk `z`) and the counter. -/
def dec (hM : need L B b d ≤ M) (z : CSL.CommonNormalizationController.Disk R B w)
    (m : Mem M w) : CSL.CommonNormalizationController.State L R B b d w × Word w :=
  (⟨fun i => m ⟨B + i.val, by unfold need at hM; omega⟩,
    fun i => m ⟨i.val, by unfold need at hM; omega⟩,
    fun i => m ⟨B + L + i.val, by unfold need at hM; omega⟩,
    fun i => m ⟨B + L + b + i.val, by unfold need at hM; omega⟩,
    fun i => m ⟨B + L + b + d + i.val, by unfold need at hM; omega⟩,
    fun i => m ⟨B + L + b + 2 * d + i.val, by unfold need at hM; omega⟩,
    m ⟨B + L + b + 3 * d, by unfold need at hM; omega⟩,
    m ⟨B + L + b + 3 * d + 1, by unfold need at hM; omega⟩,
    z⟩,
   m ⟨B + L + b + 3 * d + 2, by unfold need at hM; omega⟩)

section EncLemmas
variable (hM : need L B b d ≤ M) (s : CSL.CommonNormalizationController.State L R B b d w)
  (r : Word w)

theorem enc_buffer (i : Fin B) (h : i.val < M) : enc hM s r ⟨i.val, h⟩ = s.buffer i := by
  unfold enc; rw [dif_pos i.isLt]

theorem enc_ram (i : Fin L) (h : B + i.val < M) : enc hM s r ⟨B + i.val, h⟩ = s.ram i := by
  have := i.isLt
  unfold enc; rw [dif_neg (by first | omega | (simp; omega) | simp), dif_pos (by first | omega | (simp; omega) | simp)]
  try (congr 1; apply Fin.ext; simp)

theorem enc_scratch (i : Fin b) (h : B + L + i.val < M) :
    enc hM s r ⟨B + L + i.val, h⟩ = s.scratch i := by
  have := i.isLt
  unfold enc; rw [dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_pos (by first | omega | (simp; omega) | simp)]
  try (congr 1; apply Fin.ext; simp)

theorem enc_counter (i : Fin d) (h : B + L + b + i.val < M) :
    enc hM s r ⟨B + L + b + i.val, h⟩ = s.counter i := by
  have := i.isLt
  unfold enc
  rw [dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp),
    dif_pos (by first | omega | (simp; omega) | simp)]
  try (congr 1; apply Fin.ext; simp)

theorem enc_inputCount (i : Fin d) (h : B + L + b + d + i.val < M) :
    enc hM s r ⟨B + L + b + d + i.val, h⟩ = s.inputCount i := by
  have := i.isLt
  unfold enc
  rw [dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp),
    dif_neg (by first | omega | (simp; omega) | simp), dif_pos (by first | omega | (simp; omega) | simp)]
  try (congr 1; apply Fin.ext; simp)

theorem enc_outputCount (i : Fin d) (h : B + L + b + 2 * d + i.val < M) :
    enc hM s r ⟨B + L + b + 2 * d + i.val, h⟩ = s.outputCount i := by
  have := i.isLt
  unfold enc
  rw [dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp),
    dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_pos (by first | omega | (simp; omega) | simp)]
  try (congr 1; apply Fin.ext; simp)

theorem enc_phase (h : B + L + b + 3 * d < M) :
    enc hM s r ⟨B + L + b + 3 * d, h⟩ = s.phase := by
  unfold enc
  rw [dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp),
    dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), if_pos rfl]

theorem enc_stage (h : B + L + b + 3 * d + 1 < M) :
    enc hM s r ⟨B + L + b + 3 * d + 1, h⟩ = s.stage := by
  unfold enc
  rw [dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp),
    dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), if_neg (by first | omega | (simp; omega) | simp), if_pos rfl]

theorem enc_rem (h : B + L + b + 3 * d + 2 < M) :
    enc hM s r ⟨B + L + b + 3 * d + 2, h⟩ = r := by
  unfold enc
  rw [dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp),
    dif_neg (by first | omega | (simp; omega) | simp), dif_neg (by first | omega | (simp; omega) | simp), if_neg (by first | omega | (simp; omega) | simp), if_neg (by first | omega | (simp; omega) | simp), if_pos rfl]

end EncLemmas

theorem dec_enc (hM : need L B b d ≤ M) (z : CSL.CommonNormalizationController.Disk R B w)
    (s : CSL.CommonNormalizationController.State L R B b d w) (r : Word w) :
    dec hM z (enc hM s r) = ({s with disk := z}, r) := by
  simp only [dec, enc_buffer, enc_ram, enc_scratch, enc_counter, enc_inputCount,
    enc_outputCount, enc_phase, enc_stage, enc_rem]

/-- A small natural number as a word (used for the micro-step counter, which is at most 7). -/
def wordOf (w : ℕ) (k : ℕ) : Word w := ⟨k % 2 ^ w, Nat.mod_lt _ (by positivity)⟩

theorem wordOf_val (k : ℕ) (hk : k < 2 ^ w) : (wordOf w k).val = k := Nat.mod_eq_of_lt hk

/-- Machine block of a controller disk address. -/
def blockOf (R : ℕ) : CSL.CommonNormalizationController.Address R → ℕ
  | .inl a => a.val
  | .inr (.inl a) => R + a.val
  | .inr (.inr a) => a.val

theorem blockOf_lt (a : CSL.CommonNormalizationController.Address R) : blockOf R a < R + R := by
  rcases a with a | a | a <;> simp [blockOf] <;> omega

def off0 (M B : ℕ) : Fin (M - B + 1) := ⟨0, by omega⟩

def ioOf (M B : ℕ) : BAct (CSL.CommonNormalizationController.Address R) → IOAct M B
  | .none => .none
  | .read a => .read (blockOf R a) (off0 M B)
  | .write a => .write (off0 M B) (blockOf R a)

/-- The machine program simulating controller `p`. -/
def prog (p : CSL.CommonNormalizationController.Program L R B b d w) (hM : need L B b d ≤ M)
    (z : CSL.CommonNormalizationController.Disk R B w) : Program M B w where
  step _ m :=
    let x := dec hM z m
    if x.2.val = 0 ∧ 3 ≤ x.1.stage.val then (m, .halt)
    else
      (enc hM (micro p x.1 x.2.val).1 (wordOf w (micro p x.1 x.2.val).2.1),
        ioOf M B (microAct p x.1 x.2.val))

/-- The simulation relation between a machine configuration and a controller state with
micro-step counter `r`. -/
structure Rel (hM : need L B b d ≤ M) (c : Config M w)
    (s : CSL.CommonNormalizationController.State L R B b d w) (r : ℕ) : Prop where
  mem : c.mem = enc hM s (wordOf w r)
  halted : c.halted = false
  out : ∀ (a : Fin R) (i : Fin B), c.disk (a.val * B + i.val) = s.disk (.inr (.inr a)) i
  work : ∀ (a : Fin R) (i : Fin B), c.disk ((R + a.val) * B + i.val) = s.disk (.inr (.inl a)) i
  inp : s.stage.val ≤ 1 → ∀ a, s.disk (.inl a) = s.disk (.inr (.inr a))
  rle : r ≤ 7
  maxe : c.maxEnd ≤ (R + R) * B

theorem enc_disk (hM : need L B b d ≤ M) (s : CSL.CommonNormalizationController.State L R B b d w)
    (D : CSL.CommonNormalizationController.Disk R B w) (r : Word w) :
    enc hM {s with disk := D} r = enc hM s r := rfl

theorem enc_read (hM : need L B b d ≤ M) (s : CSL.CommonNormalizationController.State L R B b d w)
    (r : Word w) (blk : ℕ) (D : Disk w) :
    (fun i : Fin M => if (off0 M B : ℕ) ≤ i ∧ (i : ℕ) < (off0 M B : ℕ) + B then
        D (blk * B + (i - (off0 M B : ℕ))) else enc hM s r i) =
      enc hM {s with buffer := fun i => D (blk * B + i.val)} r := by
  funext i
  simp only [off0, Nat.zero_le, true_and, zero_add, Nat.sub_zero]
  unfold enc
  by_cases h : i.val < B
  · rw [if_pos h, dif_pos h]
  · rw [if_neg h, dif_neg h, dif_neg h]

/-- The disk words of a block. -/
theorem block_ext {D E : Disk w} {k : ℕ}
    (h : ∀ i : Fin B, D (k * B + i.val) = E (k * B + i.val)) (i : Fin B) :
    D (k * B + i.val) = E (k * B + i.val) := h i

theorem blocks_disjoint {x y : ℕ} (hxy : x ≠ y) (i j : Fin B) : x * B + i.val ≠ y * B + j.val := by
  intro h
  have hi := i.isLt; have hj := j.isLt
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
  · have : (x + 1) * B ≤ y * B := Nat.mul_le_mul_right B hlt
    rw [Nat.add_mul, one_mul] at this; omega
  · have : (y + 1) * B ≤ x * B := Nat.mul_le_mul_right B hgt
    rw [Nat.add_mul, one_mul] at this; omega

theorem write_word (hBM : B ≤ M) (D : Disk w) (mem' : Mem M w) (blk x : ℕ) (i : Fin B) :
    (if blk * B ≤ x * B + i.val ∧ x * B + i.val < blk * B + B then
        (if h : ((off0 M B : Fin (M - B + 1)) : ℕ) + (x * B + i.val - blk * B) < M then
          mem' ⟨(off0 M B : ℕ) + (x * B + i.val - blk * B), h⟩ else 0)
      else D (x * B + i.val)) =
      if x = blk then mem' ⟨i.val, by have := i.isLt; omega⟩ else D (x * B + i.val) := by
  have hi := i.isLt
  by_cases hx : x = blk
  · subst hx
    rw [if_pos ⟨by omega, by omega⟩, if_pos rfl, dif_pos (by simp [off0]; omega)]
    congr 1; apply Fin.ext; simp [off0]
  · rw [if_neg, if_neg hx]
    rintro ⟨h1, h2⟩
    exact blocks_disjoint hx i ⟨0, by omega⟩ (by
      have : x * B + i.val - blk * B < B := by omega
      rcases Nat.lt_or_gt_of_ne hx with hlt | hgt
      · have : (x + 1) * B ≤ blk * B := Nat.mul_le_mul_right B hlt
        rw [Nat.add_mul, one_mul] at this; omega
      · have : (blk + 1) * B ≤ x * B := Nat.mul_le_mul_right B hgt
        rw [Nat.add_mul, one_mul] at this; omega)

theorem enc_low (hM : need L B b d ≤ M) (s : CSL.CommonNormalizationController.State L R B b d w)
    (r : Word w) (i : Fin B) (h : i.val < M) : enc hM s r ⟨i.val, h⟩ = s.buffer i :=
  enc_buffer hM s r i h

/-- One machine step is one controller micro-step. -/
theorem sim_step (p : CSL.CommonNormalizationController.Program L R B b d w)
    (hM : need L B b d ≤ M) (z : CSL.CommonNormalizationController.Disk R B w)
    (c : Config M w) (s : CSL.CommonNormalizationController.State L R B b d w) (r : ℕ)
    (h : Rel hM c s r) (hnh : ¬ (r = 0 ∧ 3 ≤ s.stage.val)) :
    Rel hM (Config.step (prog p hM z) c) (micro p s r).1 (micro p s r).2.1 ∧
    (Config.step (prog p hM z) c).ios = c.ios + (micro p s r).2.2 := by
  have hcap : 8 ≤ 2 ^ w := p.phase_capacity
  have hBM : B ≤ M := by unfold need at hM; omega
  have hdec : dec hM z c.mem = ({s with disk := z}, wordOf w r) := by rw [h.mem, dec_enc]
  have hr : (wordOf w r).val = r := wordOf_val r (by have := h.rle; omega)
  have hps : (prog p hM z).step c.t c.mem =
      (enc hM (micro p {s with disk := z} r).1 (wordOf w (micro p {s with disk := z} r).2.1),
        ioOf M B (microAct p s r)) := by
    simp only [prog, hdec, hr]
    rw [if_neg (by simpa using hnh)]
    rfl
  have hspec := micro_spec p s r z
  have hmono := micro_stage_mono p s r
  have hrem := micro_rem p s r h.rle
  have hwb := fun a (ha : microAct p s r = .write a) =>
    micro_write_buffer p {s with disk := z} r a (by rw [microAct_disk]; exact ha)
  have hshape := microAct_write_shape p s r
  have hinl := microAct_read_inl p s r
  generalize hact : microAct p s r = act at hps hspec hwb hshape hinl
  generalize hm0 : micro p {s with disk := z} r = m0 at hps hspec hwb
  rw [hspec] at hmono hrem ⊢
  have hmaxb : ∀ a : CSL.CommonNormalizationController.Address R,
      blockOf R a * B + B ≤ (R + R) * B := by
    intro a
    have := blockOf_lt a
    have : (blockOf R a + 1) * B ≤ (R + R) * B := Nat.mul_le_mul_right B this
    rw [Nat.add_mul, one_mul] at this; exact this
  cases act with
  | none =>
    simp only [Config.step, h.halted, Bool.false_eq_true, if_false, hps, ioOf]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrem, ?_⟩, ?_⟩ <;> try dsimp only
    · simp only [resolve, enc_disk]
    · simp only [resolve]; exact h.out
    · simp only [resolve]; exact h.work
    · intro hs; simp only [resolve] at hs ⊢; exact h.inp (le_trans hmono hs)
    · exact h.maxe
    · simp [resolve]
  | read a =>
    simp only [Config.step, h.halted, Bool.false_eq_true, if_false, hps, ioOf]
    have hblk : (fun i : Fin B => c.disk (blockOf R a * B + i.val)) = s.disk a := by
      funext i
      rcases a with x | x | x
      · simp only [blockOf]
        rw [h.out x i, h.inp (by rw [hinl x rfl]; omega) x]
      · simp only [blockOf]; exact h.work x i
      · simp only [blockOf]; exact h.out x i
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrem, ?_⟩, ?_⟩ <;> try dsimp only
    · rw [enc_read, hblk]; simp only [resolve, enc_disk]; rfl
    · simp only [resolve]; exact h.out
    · simp only [resolve]; exact h.work
    · intro hs; simp only [resolve] at hs ⊢; exact h.inp (le_trans hmono hs)
    · exact max_le h.maxe (hmaxb a)
    · simp [resolve]
  | write a =>
    simp only [Config.step, h.halted, Bool.false_eq_true, if_false, hps, ioOf]
    have hbuf : m0.1.buffer = s.buffer := hwb a rfl
    have hw := fun (x : ℕ) (i : Fin B) => write_word hBM c.disk
      (enc hM m0.1 (wordOf w m0.2.1)) (blockOf R a) x i
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrem, ?_⟩, ?_⟩ <;> try dsimp only
    · simp only [resolve, enc_disk]
    · intro x i
      rw [hw, enc_low, hbuf]
      simp only [resolve]
      rcases hshape a rfl with ⟨y, rfl⟩ | ⟨_, y, rfl⟩
      · rw [if_neg (by simp only [blockOf]; omega), h.out x i, Function.update_of_ne (by simp)]
      · by_cases hxy : x.val = y.val
        · rw [if_pos (by simp only [blockOf]; exact hxy), show x = y from Fin.ext hxy,
            Function.update_self]
        · rw [if_neg (by simp only [blockOf]; exact hxy), h.out x i, Function.update_of_ne (by
            intro he; apply hxy; simp at he; rw [he])]
    · intro x i
      rw [hw, enc_low, hbuf]
      simp only [resolve]
      rcases hshape a rfl with ⟨y, rfl⟩ | ⟨_, y, rfl⟩
      · by_cases hxy : x.val = y.val
        · rw [if_pos (by simp only [blockOf]; omega), show x = y from Fin.ext hxy,
            Function.update_self]
        · rw [if_neg (by simp only [blockOf]; omega), h.work x i, Function.update_of_ne (by
            intro he; apply hxy; simp at he; rw [he])]
      · rw [if_neg (by simp only [blockOf]; omega), h.work x i, Function.update_of_ne (by simp)]
    · intro hs a'
      simp only [resolve] at hs ⊢
      have hs0 : s.stage.val ≤ 1 := le_trans hmono hs
      rcases hshape a rfl with ⟨y, rfl⟩ | ⟨h2, y, rfl⟩
      · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
        exact h.inp hs0 a'
      · omega
    · exact max_le h.maxe (hmaxb a)
    · simp [resolve]

/-- The program with an initialization step: at step `0` it writes the encoding of the initial
controller state `s0` (with counter `0`) into memory, without any transfer. -/
def prog' (p : CSL.CommonNormalizationController.Program L R B b d w) (hM : need L B b d ≤ M)
    (z : CSL.CommonNormalizationController.Disk R B w)
    (s0 : CSL.CommonNormalizationController.State L R B b d w) : Program M B w where
  step t m := if t = 0 then (enc hM s0 (wordOf w 0), .none) else (prog p hM z).step t m

theorem micro_halt (p : CSL.CommonNormalizationController.Program L R B b d w)
    (s : CSL.CommonNormalizationController.State L R B b d w) (h : 3 ≤ s.stage.val) :
    micro p s 0 = (s, 0, 0) := by
  unfold micro
  simp only [if_true]
  rcases hk : s.stage.val with _ | _ | _ | k
  · omega
  · omega
  · omega
  · rfl

/-- Invariant of the machine run: either the simulation relation, or the machine has halted
in the terminal stage with the output region in place. -/
def Good (hM : need L B b d ≤ M) (c : Config M w)
    (s : CSL.CommonNormalizationController.State L R B b d w) (r cost : ℕ) : Prop :=
  (Rel hM c s r ∨
    (c.halted = true ∧ r = 0 ∧ 3 ≤ s.stage.val ∧
      (∀ (a : Fin R) (i : Fin B), c.disk (a.val * B + i.val) = s.disk (.inr (.inr a)) i) ∧
      c.maxEnd ≤ (R + R) * B)) ∧
  c.ios = cost ∧ 1 ≤ c.t

theorem good_step (p : CSL.CommonNormalizationController.Program L R B b d w)
    (hM : need L B b d ≤ M) (z : CSL.CommonNormalizationController.Disk R B w)
    (s0 : CSL.CommonNormalizationController.State L R B b d w)
    (c : Config M w) (s : CSL.CommonNormalizationController.State L R B b d w) (r cost : ℕ)
    (h : Good hM c s r cost) :
    Good hM (Config.step (prog' p hM z s0) c) (micro p s r).1 (micro p s r).2.1
      (cost + (micro p s r).2.2) := by
  obtain ⟨hrel | ⟨hh, hr0, hst, hout, hme⟩, hios, ht⟩ := h
  · have hstepeq : Config.step (prog' p hM z s0) c = Config.step (prog p hM z) c := by
      unfold Config.step
      have : (prog' p hM z s0).step c.t c.mem = (prog p hM z).step c.t c.mem := by
        simp only [prog']; rw [if_neg (by omega)]
      rw [this]
    rw [hstepeq]
    by_cases hnh : r = 0 ∧ 3 ≤ s.stage.val
    · -- halt
      obtain ⟨hr0, hst⟩ := hnh
      subst hr0
      rw [micro_halt p s hst]
      have hdec : dec hM z c.mem = ({s with disk := z}, wordOf w 0) := by rw [hrel.mem, dec_enc]
      have hw0 : (wordOf w 0).val = 0 := wordOf_val 0 (by positivity)
      have hps : (prog p hM z).step c.t c.mem = (c.mem, .halt) := by
        simp only [prog, hdec, hw0]
        simp [hst]
      refine ⟨Or.inr ⟨?_, by simp, hst, ?_, ?_⟩, ?_, ?_⟩
      · simp [Config.step, hrel.halted, hps]
      · intro a i; simp only [Config.step, hrel.halted, Bool.false_eq_true, if_false, hps]
        exact hrel.out a i
      · simp only [Config.step, hrel.halted, Bool.false_eq_true, if_false, hps]; exact hrel.maxe
      · simp only [Config.step, hrel.halted, Bool.false_eq_true, if_false, hps]; omega
      · simp only [Config.step, hrel.halted, Bool.false_eq_true, if_false, hps]; omega
    · obtain ⟨hr', hio⟩ := sim_step p hM z c s r hrel hnh
      refine ⟨Or.inl hr', by rw [hio, hios], ?_⟩
      have : (Config.step (prog p hM z) c).t = c.t + 1 := by
        unfold Config.step; rw [if_neg (by rw [hrel.halted]; decide)]
        split <;> rfl
      omega
  · subst hr0
    rw [micro_halt p s hst]
    have hc : Config.step (prog' p hM z s0) c = c := by
      unfold Config.step; rw [if_pos hh]
    rw [hc]
    exact ⟨Or.inr ⟨hh, by simp, hst, hout, hme⟩, by simp [hios], ht⟩

theorem good_iter (p : CSL.CommonNormalizationController.Program L R B b d w)
    (hM : need L B b d ≤ M) (z : CSL.CommonNormalizationController.Disk R B w)
    (s0 : CSL.CommonNormalizationController.State L R B b d w) (n : ℕ) :
    ∀ (c : Config M w) (s : CSL.CommonNormalizationController.State L R B b d w) (r cost : ℕ),
    Good hM c s r cost →
    Good hM ((Config.step (prog' p hM z s0))^[n] c) (iter p n s r).1 (iter p n s r).2.1
      (cost + (iter p n s r).2.2) := by
  induction n with
  | zero => intro c s r cost h; simpa [iter] using h
  | succ n ih =>
    intro c s r cost h
    have h1 := good_step p hM z s0 c s r cost h
    have h2 := ih _ _ _ _ h1
    rw [Function.iterate_succ_apply]
    rw [iter_succ]
    simpa only [Nat.add_assoc] using h2

end CSLB.NormalBridge


