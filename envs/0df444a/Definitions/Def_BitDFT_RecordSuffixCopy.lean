-- Prove2me | Definitions.Def_BitDFT_RecordSuffixCopy
-- name    : BitDFT_RecordSuffixCopy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T19:59:18.304395+00:00
-- url     : https://prove2.me/theorems/099b6ebb-277e-4526-90a6-a6a4adc2d2e4
-- title:
--   Embed the two-tape copier into a caller workspace
-- statement:
--   A two-tape bit-suffix copier is embedded into a caller's record workspace. The caller's input and output tapes are routed to the copier's two active tapes, while the remaining tape contents and head positions are carried as parked workspace. The embedding preserves machine steps exactly.
-- source:
--   Machine-level bridge from a separator-terminated signed coordinate record to the low-precision integer multiplier input.

import Definitions.Def_BitDFT_RecordTerminator
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Definitions.Def_BitDFT_AlphabetEmbedding
import Definitions.Def_BitDFT_WorkRelocation
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapeCountTransport
import Definitions.Def_BitDFT_TapePermutation
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_count_transport_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Theorems.Thm_BitDFT_work_relocation_correct

noncomputable section
namespace BitDFT.RecordSuffixCopy
open IntMul BitDFT.RecordTerminator BitDFT.MachineSequence

abbrev host (M : MultitapeTM) := RecordTerminator.storage M
abbrev sourceTape (M : MultitapeTM) : Fin (host M).k := RecordTerminator.target M

def encode (M : MultitapeTM) : TapeCopy.Sym → (host M).Sym
  | .blank => (host M).blank
  | .start => (host M).startSym
  | .zero => (host M).zero
  | .one => (host M).one
  | .sep => (host M).sep

def alphabetMap (M : MultitapeTM) :
    AlphabetEmbedding.Map SuffixCopyTwoTape.machine (host M) where
  encode := {
    toFun := encode M
    inj' := by
      intro a b hab
      have hd := (host M).syms_distinct
      simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at hd
      cases a <;> cases b <;> simp_all [encode]
  }
  blank := rfl
  marker := rfl
  zero := rfl
  one := rfl
  sep := rfl

abbrev encoded (M : MultitapeTM) := AlphabetEmbedding.machine (alphabetMap M)
abbrev relocated (M : MultitapeTM) := WorkRelocation.machine (encoded M)
abbrev rawExtended (M : MultitapeTM) :=
  TapeExtension.machine (relocated M) ((host M).k - 3)

private theorem host_ge_three (M : MultitapeTM) : 3 ≤ (host M).k := by
  have hs := (sourceTape M).isLt
  have hv : (sourceTape M).val = M.k + 7 := rfl
  have hm := M.two_le_k
  omega

theorem extension_count (M : MultitapeTM) : (rawExtended M).k = (host M).k := by
  change 3 + ((host M).k - 3) = (host M).k
  have h := host_ge_three M
  omega

abbrev extended (M : MultitapeTM) :=
  TapeCountTransport.machine (rawExtended M) (host M).k (extension_count M)

private theorem source_ne_zero (M : MultitapeTM) :
    sourceTape M ≠ (⟨0, by have := host_ge_three M; omega⟩ : Fin (host M).k) := by
  intro h
  have hv := congrArg Fin.val h
  simp [sourceTape,RecordTerminator.target,SignedBlockPlacement.scratchTape] at hv

private theorem source_ne_one (M : MultitapeTM) :
    sourceTape M ≠ (⟨1, by have := host_ge_three M; omega⟩ : Fin (host M).k) := by
  intro h
  have hv := congrArg Fin.val h
  simp [sourceTape,RecordTerminator.target,SignedBlockPlacement.scratchTape] at hv

private theorem source_ne_two (M : MultitapeTM) :
    sourceTape M ≠ (⟨2, by have := host_ge_three M; omega⟩ : Fin (host M).k) := by
  intro h
  have hv := congrArg Fin.val h
  simp [sourceTape,RecordTerminator.target,SignedBlockPlacement.scratchTape] at hv

def routing (M : MultitapeTM) : Fin (host M).k ≃ Fin (host M).k :=
  (Equiv.swap (⟨2, by have := host_ge_three M; omega⟩) (sourceTape M)).trans
    (Equiv.swap (⟨1, by have := host_ge_three M; omega⟩) (sourceTape M))

theorem routing_zero (M : MultitapeTM) :
    routing M (host M).inTape = (host M).inTape := by
  change routing M ⟨0,by have := (host M).two_le_k; omega⟩ = ⟨0,by have := (host M).two_le_k; omega⟩
  simp only [routing,Equiv.trans_apply]
  have h0s := (source_ne_zero M).symm
  have h02 : (⟨0, by have := host_ge_three M; omega⟩ : Fin (host M).k) ≠ ⟨2, by have := host_ge_three M; omega⟩ := by
    intro h; have hv := congrArg Fin.val h; simp at hv
  rw [Equiv.swap_apply_of_ne_of_ne h02 h0s]
  have h01 : (⟨0, by have := host_ge_three M; omega⟩ : Fin (host M).k) ≠ ⟨1, by have := host_ge_three M; omega⟩ := by
    intro h; have hv := congrArg Fin.val h; simp at hv
  rw [Equiv.swap_apply_of_ne_of_ne h01 h0s]

theorem routing_one (M : MultitapeTM) :
    routing M (⟨1, by have := host_ge_three M; omega⟩ : Fin (host M).k) = sourceTape M := by
  simp only [routing,Equiv.trans_apply]
  have h1s := (source_ne_one M).symm
  have h12 : (⟨1, by have := host_ge_three M; omega⟩ : Fin (host M).k) ≠ ⟨2, by have := host_ge_three M; omega⟩ := by
    intro h; have hv := congrArg Fin.val h; simp at hv
  rw [Equiv.swap_apply_of_ne_of_ne h12 h1s]
  rw [Equiv.swap_apply_left]

theorem routing_two (M : MultitapeTM) :
    routing M (⟨2, by have := host_ge_three M; omega⟩ : Fin (host M).k) = (host M).outTape := by
  apply Fin.ext
  simp only [routing,Equiv.trans_apply]
  rw [Equiv.swap_apply_left]
  rw [Equiv.swap_apply_right]
  rfl

theorem routing_input (M : MultitapeTM) :
    routing M (extended M).inTape = (extended M).inTape := by
  apply Fin.ext
  have h := congrArg Fin.val (routing_zero M)
  simpa [MultitapeTM.inTape] using h

abbrev routed (M : MultitapeTM) :=
  TapePermutation.machine (extended M) (routing M) (routing_input M)

def control (M : MultitapeTM) : Controller (host M) where
  K := (routed M).K
  entry := (routed M).qStart
  exit := (routed M).qHalt
  distinct := (routed M).start_ne_halt
  transition := (routed M).δ
  marker := (routed M).start_preserved
  noMarker := (routed M).start_only_at_start
  frozen := (routed M).halt_fixed
  readonly := (routed M).input_readonly

abbrev composedController (M : MultitapeTM) :=
  BitDFT.MachineSequence.sequence
    (BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (RecordTerminator.control M))
    (control M)

abbrev machine (M : MultitapeTM) := (composedController M).machine

def embed (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (c : SuffixCopyTwoTape.machine.Cfg) : (routed M).Cfg :=
  TapePermutation.embed (extended M) (routing M) (routing_input M)
    (TapeCountTransport.embed (rawExtended M) (host M).k (extension_count M)
      (TapeExtension.embed (relocated M) ((host M).k - 3)
        (fun i => cells (routing M (Fin.cast (extension_count M) i)))
        (fun i => heads (routing M (Fin.cast (extension_count M) i)))
        (WorkRelocation.embed (encoded M) rootCells rootHead
          (AlphabetEmbedding.embed (alphabetMap M) c))))

theorem run_embed (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (c : SuffixCopyTwoTape.machine.Cfg) (t : ℕ) :
    (routed M).step^[t] (embed M cells heads rootCells rootHead c) =
      embed M cells heads rootCells rootHead (SuffixCopyTwoTape.machine.step^[t] c) := by
  unfold embed
  rw [BitDFT.tape_permutation_run,
    BitDFT.tape_count_transport_correct,
    (BitDFT.tape_extension_correct (relocated M) ((host M).k - 3)).1,
    (BitDFT.work_relocation_correct (encoded M) rootCells rootHead _ t).1,
    (BitDFT.alphabet_embedding_correct SuffixCopyTwoTape.machine (host M)
      (alphabetMap M)).1]

end BitDFT.RecordSuffixCopy


