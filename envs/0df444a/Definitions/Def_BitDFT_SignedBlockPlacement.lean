-- Prove2me | Definitions.Def_BitDFT_SignedBlockPlacement
-- name    : BitDFT_SignedBlockPlacement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:49:10.791987+00:00
-- url     : https://prove2.me/theorems/9f288a5b-7caf-4efe-b6fb-5671727b0322
-- title:
--   Route signed-coordinate extraction to the vector and prepared descriptors
-- statement:
--   Embed the signed-record extractor in an arbitrary machine alphabet, with extra tapes and a fixed permutation. The native input stays on tape zero, the vector stays on tape one, the scratch destination is tape k+7, and the counter and template are tapes k+5 and k+6. Other tapes are parked. This defines the extraction phase; its explicit initial configuration remains a prerequisite.
-- source:
--   Placement of charged descriptor initialization in the exact DFT output scaler.

import Definitions.Def_BitDFT_SignedBlock
import Definitions.Def_BitDFT_WorkRelocation
import Definitions.Def_BitDFT_PreprocessorAlphabet
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapePermutation
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
namespace BitDFT.SignedBlockPlacement
open IntMul
abbrev storage := WorkRelocation.machine SignedBlock.machine

def alphabetMap (N : MultitapeTM) : AlphabetEmbedding.Map storage N where
  encode := (PreprocessorAlphabet.alphabetMap N).encode
  blank := rfl
  marker := rfl
  zero := rfl
  one := rfl
  sep := rfl

abbrev lifted (N : MultitapeTM) := AlphabetEmbedding.machine (alphabetMap N)
abbrev extended (N : MultitapeTM) (k : ℕ) := TapeExtension.machine (lifted N) (k+3)

def scratchTape (k : ℕ) : Fin (5+(k+3)) := ⟨k+7,by omega⟩
def counterTape (k : ℕ) : Fin (5+(k+3)) := ⟨k+5,by omega⟩
def templateTape (k : ℕ) : Fin (5+(k+3)) := ⟨k+6,by omega⟩

def routing (k : ℕ) : Fin (5+(k+3)) ≃ Fin (5+(k+3)) :=
  ((Equiv.swap ⟨2,by omega⟩ (scratchTape k)).trans (Equiv.swap ⟨3,by omega⟩ (counterTape k))).trans
    (Equiv.swap ⟨4,by omega⟩ (templateTape k))

theorem routing_zero (k : ℕ) : routing k ⟨0,by omega⟩ = ⟨0,by omega⟩ := by
  simp [routing,Equiv.swap_apply_def,scratchTape,counterTape,templateTape,Fin.ext_iff]

theorem routing_one (k : ℕ) : routing k ⟨1,by omega⟩ = ⟨1,by omega⟩ := by
  simp [routing,Equiv.swap_apply_def,scratchTape,counterTape,templateTape,Fin.ext_iff]

theorem routing_two (k : ℕ) : routing k ⟨2,by omega⟩ = scratchTape k := by
  simp [routing,Equiv.swap_apply_def,scratchTape,counterTape,templateTape,Fin.ext_iff]

theorem routing_three (k : ℕ) : routing k ⟨3,by omega⟩ = counterTape k := by
  simp [routing,Equiv.swap_apply_def,scratchTape,counterTape,templateTape,Fin.ext_iff]

theorem routing_four (k : ℕ) : routing k ⟨4,by omega⟩ = templateTape k := by
  simp [routing,Equiv.swap_apply_def,scratchTape,counterTape,templateTape,Fin.ext_iff]

theorem routing_input (N : MultitapeTM) (k : ℕ) :
    routing k (extended N k).inTape = (extended N k).inTape := routing_zero k

abbrev machine (N : MultitapeTM) (k : ℕ) :=
  TapePermutation.machine (extended N k) (routing k) (routing_input N k)

/-- Extra tape data is supplied in physical tape order and remains parked. -/
def embed (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (c : storage.Cfg) : (machine N k).Cfg :=
  TapePermutation.embed (extended N k) (routing k) (routing_input N k)
    (TapeExtension.embed (lifted N) (k+3)
      (fun i => cells (routing k i)) (fun i => heads (routing k i))
      (AlphabetEmbedding.embed (alphabetMap N) c))
end BitDFT.SignedBlockPlacement


