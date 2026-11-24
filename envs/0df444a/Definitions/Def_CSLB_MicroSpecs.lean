-- Prove2me | Definitions.Def_CSLB_MicroSpecs
-- name    : CSLB_MicroSpecs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:43:53.986122+00:00
-- url     : https://prove2.me/theorems/99d1928a-95dd-4c90-a104-2273c68d7c88
-- title:
--   Coded sorting bridge: MicroSpecs
-- statement:
--   # Every micro-step of the normalization controller is one block transfer
--
--   The three inner machines of `CommonNormalizationController` (input expansion, the fixed policy
--   core, and output compaction) change their state one phase at a time. This module shows that
--   each such micro-step either leaves the disk untouched and does not look at it, or reads one
--   block into the transfer buffer, or writes the transfer buffer to one block; the address is
--   determined by the resident state. Concretely, the step on a state with disk `D` equals the
--   step on the same resident state with an arbitrary disk `z`, followed by the read or write.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSL_Shared_Memory_NormalizationController

/-! # Every micro-step of the normalization controller is one block transfer

The three inner machines of `CommonNormalizationController` (input expansion, the fixed policy
core, and output compaction) change their state one phase at a time. This module shows that
each such micro-step either leaves the disk untouched and does not look at it, or reads one
block into the transfer buffer, or writes the transfer buffer to one block; the address is
determined by the resident state. Concretely, the step on a state with disk `D` equals the
step on the same resident state with an arbitrary disk `z`, followed by the read or write. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CSLB.MicroSpecs
open CSL

/-- A resolved block action on a disk indexed by `α`: `none`, read of block `a`, write to
block `a`. -/
inductive BAct (α : Type) where
  | none
  | read (a : α)
  | write (a : α)

section Layout
open CSL.PhysicalNormalizationLayout
variable {R B b d w : ℕ}

/-- The block action of one expansion micro-step. -/
def layoutAct (p : Program R B b d w) (t : State R B b d w) : BAct (Address R) :=
  if current t < p.blocks then
    match t.phase.val with
    | 1 => .read (.inl (index p (current t * b / B)))
    | 3 => .read (.inl (index p (current t * b / B + 1)))
    | 6 => .write (.inr (index p (current t)))
    | _ => .none
  else .none

theorem layout_spec (p : Program R B b d w) (t : State R B b d w) (z : Disk R B w) :
    step p t =
      match layoutAct p t with
      | .none => ({(step p {t with disk := z}).1 with disk := t.disk}, 0)
      | .read a => ({(step p {t with disk := z}).1 with buffer := t.disk a, disk := t.disk}, 1)
      | .write a => ({(step p {t with disk := z}).1 with disk := Function.update t.disk a t.buffer}, 1) := by
  unfold step layoutAct current
  by_cases h : WordControl.decodeWords t.counter < p.blocks
  · simp only [h, if_true]
    generalize hk : t.phase.val = k
    rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp [nextPhase]
  · simp only [h, if_false]

theorem layout_write_buffer (p : Program R B b d w) (t : State R B b d w)
    (a : Address R) (h : layoutAct p t = .write a) : (step p t).1.buffer = t.buffer := by
  unfold layoutAct at h
  unfold step
  by_cases hc : current t < p.blocks
  · simp only [current] at hc h ⊢
    simp only [hc, if_true] at h ⊢
    generalize hk : t.phase.val = k at h ⊢
    rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp_all [nextPhase]
  · simp only [current] at hc h
    simp [hc] at h

end Layout

section Compact
open CSL.PhysicalNormalizationLayout
variable {R B b d w : ℕ}

/-- The block action of one compaction micro-step. -/
def compactAct (p : Program R B b d w) (t : State R B b d w) : BAct (Address R) :=
  if current t < p.blocks then
    match t.phase.val with
    | 0 => .read (.inl (index p (current t)))
    | 2 => .read (.inr (index p (current t * b / B)))
    | 4 => .write (.inr (index p (current t * b / B)))
    | 5 => .read (.inr (index p (current t * b / B + 1)))
    | 7 => .write (.inr (index p (current t * b / B + 1)))
    | _ => .none
  else .none

theorem compact_spec (p : Program R B b d w) (t : State R B b d w) (z : Disk R B w) :
    PhysicalNormalizationCompact.step p t =
      match compactAct p t with
      | .none => ({(PhysicalNormalizationCompact.step p {t with disk := z}).1 with disk := t.disk}, 0)
      | .read a => ({(PhysicalNormalizationCompact.step p {t with disk := z}).1 with
          buffer := t.disk a, disk := t.disk}, 1)
      | .write a => ({(PhysicalNormalizationCompact.step p {t with disk := z}).1 with
          disk := Function.update t.disk a t.buffer}, 1) := by
  unfold PhysicalNormalizationCompact.step compactAct current
  by_cases h : WordControl.decodeWords t.counter < p.blocks
  · simp only [h, if_true]
    generalize hk : t.phase.val = k
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [nextPhase]
  · simp only [h, if_false]

theorem compact_write_buffer (p : Program R B b d w) (t : State R B b d w)
    (a : Address R) (h : compactAct p t = .write a) :
    (PhysicalNormalizationCompact.step p t).1.buffer = t.buffer := by
  unfold compactAct at h
  unfold PhysicalNormalizationCompact.step
  by_cases hc : current t < p.blocks
  · simp only [current] at hc h ⊢
    simp only [hc, if_true] at h ⊢
    generalize hk : t.phase.val = k at h ⊢
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all [nextPhase]
  · simp only [current] at hc h
    simp [hc] at h

end Compact

section Core
open CSL.FixedPolicyNormalization CSL.Normalization
variable {L b B D w : ℕ}

/-- The block action of one micro-step of the fixed-policy core. -/
def coreAct (p : Program L b D w) (s : State L B D w) : BAct (Fin D) :=
  match s.phase.val with
  | 0 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .read address _ => .read address
      | _ => .none
    | none => .none
  | 2 => match p.policy s.data.ram with
    | some i => match i.operation with
      | .write address _ => .write address
      | _ => .none
    | none => .none
  | _ => .none

theorem core_spec (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w) (p : Program L b D w)
    (s : State L B D w) (z : Normalization.Disk D B (Word w)) :
    step hb hcap padding p s =
      match coreAct p s with
      | .none => ({(step hb hcap padding p ⟨{s.data with disk := z}, s.phase⟩).1 with
          data := {(step hb hcap padding p ⟨{s.data with disk := z}, s.phase⟩).1.data with
            disk := s.data.disk}}, 0)
      | .read a => ({(step hb hcap padding p ⟨{s.data with disk := z}, s.phase⟩).1 with
          data := {(step hb hcap padding p ⟨{s.data with disk := z}, s.phase⟩).1.data with
            buffer := s.data.disk a, disk := s.data.disk}}, 1)
      | .write a => ({(step hb hcap padding p ⟨{s.data with disk := z}, s.phase⟩).1 with
          data := {(step hb hcap padding p ⟨{s.data with disk := z}, s.phase⟩).1.data with
            disk := Function.update s.data.disk a s.data.buffer}}, 1) := by
  unfold step coreAct
  generalize hk : s.phase.val = k
  rcases k with _ | _ | _ | k
  · simp only
    cases hp : p.policy s.data.ram with
    | none => simp [ready]
    | some i =>
      simp only
      cases i.operation <;> simp [ready]
  · simp only
    cases hp : p.policy s.data.ram with
    | none => simp [ready]
    | some i =>
      simp only
      cases i.operation <;> simp [ready]
  · simp only
    cases hp : p.policy s.data.ram with
    | none => simp [ready]
    | some i =>
      simp only
      cases i.operation <;> simp [ready]
  · simp [ready]

theorem core_write_buffer (hb : b ≤ B) (hcap : 4 ≤ 2^w) (padding : Word w) (p : Program L b D w)
    (s : State L B D w) (a : Fin D) (h : coreAct p s = .write a) :
    (step hb hcap padding p s).1.data.buffer = s.data.buffer := by
  unfold coreAct at h
  unfold step
  generalize hk : s.phase.val = k at h ⊢
  rcases k with _ | _ | _ | k
  · cases hp : p.policy s.data.ram with
    | none => simp [hp] at h
    | some i =>
      simp only [hp] at h ⊢
      cases ho : i.operation <;> simp_all
  · simp at h
  · cases hp : p.policy s.data.ram with
    | none => simp [hp] at h
    | some i =>
      simp only [hp] at h ⊢
      cases ho : i.operation <;> simp_all [ready]
  · simp at h

end Core

end CSLB.MicroSpecs


