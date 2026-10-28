-- Prove2me | Definitions.Def_BitDFT_DescriptorPlacement
-- name    : BitDFT_DescriptorPlacement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:14:07.063655+00:00
-- url     : https://prove2.me/theorems/0dd3ed6b-2b00-4209-9da0-f261bb0fad02
-- title:
--   Place descriptor preparation on saved precision and fresh counter tapes
-- statement:
--   Lift the rewind-and-descriptor routine into a chosen finite alphabet, add parked work tapes, and permute its tape indices. For a child tape count k at least two, source tape one is placed at k+3, and its two destinations at k+5 and k+6. Native tape zero remains fixed. Other physical tapes retain explicitly supplied contents and heads. This is a machine wiring construction, not a free copying operation.
-- source:
--   Placement of charged descriptor initialization in the exact DFT output scaler.

import Definitions.Def_BitDFT_RewoundDescriptor
import Definitions.Def_BitDFT_PreprocessorAlphabet
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapePermutation
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
namespace BitDFT.DescriptorPlacement
open IntMul

def alphabetMap (N : MultitapeTM) : AlphabetEmbedding.Map RewoundDescriptor.machine N where
  encode := (PreprocessorAlphabet.alphabetMap N).encode
  blank := rfl
  marker := rfl
  zero := rfl
  one := rfl
  sep := rfl

abbrev lifted (N : MultitapeTM) := AlphabetEmbedding.machine (alphabetMap N)
abbrev extended (N : MultitapeTM) (k : ℕ) := TapeExtension.machine (lifted N) (k+3)

def precisionTape (k : ℕ) : Fin (4+(k+3)) := ⟨k+3,by omega⟩
def counterTape (k : ℕ) : Fin (4+(k+3)) := ⟨k+5,by omega⟩
def templateTape (k : ℕ) : Fin (4+(k+3)) := ⟨k+6,by omega⟩

def routing (k : ℕ) : Fin (4+(k+3)) ≃ Fin (4+(k+3)) :=
  ((Equiv.swap ⟨1,by omega⟩ (precisionTape k)).trans (Equiv.swap ⟨2,by omega⟩ (counterTape k))).trans
    (Equiv.swap ⟨3,by omega⟩ (templateTape k))

theorem routing_zero (k : ℕ) : routing k ⟨0,by omega⟩ = ⟨0,by omega⟩ := by
  simp [routing,Equiv.swap_apply_def,precisionTape,counterTape,templateTape,Fin.ext_iff]

theorem routing_one (k : ℕ) (hk : 2 ≤ k) : routing k ⟨1,by omega⟩ = precisionTape k := by
  simp [routing,Equiv.swap_apply_def,precisionTape,counterTape,templateTape,Fin.ext_iff]
  omega

theorem routing_two (k : ℕ) (hk : 2 ≤ k) : routing k ⟨2,by omega⟩ = counterTape k := by
  have hm : 1 % (4+(k+3)) = 1 := Nat.mod_eq_of_lt (by omega)
  simp [routing,Equiv.swap_apply_def,precisionTape,counterTape,templateTape,Fin.ext_iff,hm]

theorem routing_three (k : ℕ) (hk : 2 ≤ k) : routing k ⟨3,by omega⟩ = templateTape k := by
  have hm : 1 % (4+(k+3)) = 1 := Nat.mod_eq_of_lt (by omega)
  have hk0 : k ≠ 0 := by omega
  simp [routing,Equiv.swap_apply_def,precisionTape,counterTape,templateTape,Fin.ext_iff,hm,hk0]

theorem routing_input (N : MultitapeTM) (k : ℕ) :
    routing k (extended N k).inTape = (extended N k).inTape := routing_zero k

abbrev machine (N : MultitapeTM) (k : ℕ) :=
  TapePermutation.machine (extended N k) (routing k) (routing_input N k)

/-- Extra tape data is supplied in physical tape order and remains parked. -/
def embed (N : MultitapeTM) (k : ℕ)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (c : RewoundDescriptor.machine.Cfg) : (machine N k).Cfg :=
  TapePermutation.embed (extended N k) (routing k) (routing_input N k)
    (TapeExtension.embed (lifted N) (k+3)
      (fun i => cells (routing k i)) (fun i => heads (routing k i))
      (AlphabetEmbedding.embed (alphabetMap N) c))
end BitDFT.DescriptorPlacement


