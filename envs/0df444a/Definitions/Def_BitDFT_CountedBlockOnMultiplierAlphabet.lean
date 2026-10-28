-- Prove2me | Definitions.Def_BitDFT_CountedBlockOnMultiplierAlphabet
-- name    : BitDFT_CountedBlockOnMultiplierAlphabet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T04:46:53.668289+00:00
-- url     : https://prove2.me/theorems/cf1f44c2-ff59-4a9b-8219-9ebfa1c2d91c
-- title:
--   Run the counted serializer in the multiplier alphabet
-- statement:
--   For any multitape machine alphabet, embed the counted-block serializer's five distinguished symbols into that alphabet, then run its four logical tapes on work tapes 1 through 4 of a five-tape controller. Tape 0 remains the controller's read-only input.
-- source:
--   This adapts the counted-block finite controller to an arbitrary multiplier alphabet using the existing distinguished-symbol embedding, and relocates its source tape away from the host input tape.

import Definitions.Def_BitDFT_CountedBlock
import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_AlphabetEmbedding
import Definitions.Def_BitDFT_PreprocessorAlphabet

set_option autoImplicit false
noncomputable section

namespace BitDFT.CountedBlockOnMultiplierAlphabet
open IntMul BitDFT.MachineSequence

private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

abbrev sourceMachine := CountedStream.machine

def alphabetMap (M : MultitapeTM) : AlphabetEmbedding.Map sourceMachine M where
  encode := (BitDFT.PreprocessorAlphabet.alphabetMap M).encode
  blank := rfl
  marker := rfl
  zero := rfl
  one := rfl
  sep := rfl

abbrev storage (M : MultitapeTM) := AlphabetEmbedding.machine (alphabetMap M)

abbrev host (M : MultitapeTM) : MultitapeTM where
  Sym := M.Sym
  blank := M.blank
  startSym := M.startSym
  zero := M.zero
  one := M.one
  sep := M.sep
  syms_distinct := M.syms_distinct
  K := Bool
  qStart := false
  qHalt := true
  start_ne_halt := by decide
  k := 5
  two_le_k := by decide
  δ := fun _ a => (true, fun i => (a i, .stay))
  start_preserved := by
    intro q a i hi
    exact ⟨hi, by change Move.stay ≠ Move.left; decide⟩
  start_only_at_start := by intro q a i hi; exact hi
  halt_fixed := by intro a; rfl
  input_readonly := by intro q a; rfl

def workTape (i : Fin 4) : Fin 5 := ⟨i.val + 1, by omega⟩
def hostToWork (j : Fin 5) : Fin 4 := ⟨j.val - 1, by have := j.isLt; omega⟩

theorem workTape_hostToWork (j : Fin 5) (hj : 0 < j.val) :
    workTape (hostToWork j) = j := by
  apply Fin.ext
  simp [workTape, hostToWork]
  omega

def transition (M : MultitapeTM) (q : (storage M).K)
    (a : Fin 5 → (host M).Sym) :
    (storage M).K × (Fin 5 → (host M).Sym × Move) := by
  classical
  let inner : Fin 4 → (storage M).Sym := fun i => a (workTape i)
  let r := (storage M).δ q inner
  exact (r.1, fun j => if h0 : j = 0 then (a j, .stay)
    else if hp : j.val < 5 then r.2 (hostToWork j) else (a j, .stay))

def controller (M : MultitapeTM) : Controller (host M) where
  K := (storage M).K
  entry := (storage M).qStart
  exit := (storage M).qHalt
  distinct := (storage M).start_ne_halt
  transition := transition M
  marker := by
    intro q a j hj
    by_cases h0 : j = 0
    · subst j
      simp [transition, hj]
    · have hval : j.val ≠ 0 := by intro hv; exact h0 (Fin.ext hv)
      have hp : 0 < j.val := Nat.pos_of_ne_zero hval
      have hj5 : j.val < 5 := j.isLt
      have hinner : (fun i : Fin 4 => a (workTape i)) (hostToWork j) =
          (storage M).startSym := by
        change a (workTape (hostToWork j)) = (storage M).startSym
        rw [workTape_hostToWork j hp]
        exact hj
      have hm := (storage M).start_preserved q (fun i : Fin 4 => a (workTape i))
        (hostToWork j) hinner
      simpa [transition, h0, hj5, storage, AlphabetEmbedding.machine] using hm
  noMarker := by
    intro q a j hj
    by_cases h0 : j = 0
    · subst j
      simp [transition, hj]
    · have hval : j.val ≠ 0 := by intro hv; exact h0 (Fin.ext hv)
      have hp : 0 < j.val := Nat.pos_of_ne_zero hval
      have hj5 : j.val < 5 := j.isLt
      have hinner : (fun i : Fin 4 => a (workTape i)) (hostToWork j) ≠
          (storage M).startSym := by
        change a (workTape (hostToWork j)) ≠ (storage M).startSym
        rw [workTape_hostToWork j hp]
        exact hj
      have hm := (storage M).start_only_at_start q
        (fun i : Fin 4 => a (workTape i)) (hostToWork j) hinner
      simpa [transition, h0, hj5] using hm
  frozen := by
    intro a
    have h := (storage M).halt_fixed (fun i : Fin 4 => a (workTape i))
    apply Prod.ext
    · simpa [transition] using congrArg Prod.fst h
    · funext j
      by_cases h0 : j = 0
      · subst j
        simp [transition]
      · have hval : j.val ≠ 0 := by intro hv; exact h0 (Fin.ext hv)
        have hp : 0 < j.val := Nat.pos_of_ne_zero hval
        have hj5 : j.val < 5 := j.isLt
        simpa [transition, h0, hj5, workTape_hostToWork j hp] using
          congrFun (congrArg Prod.snd h) (hostToWork j)
  readonly := by
    intro q a
    simp [transition, MultitapeTM.inTape]

abbrev machine (M : MultitapeTM) := (controller M).machine

def embed (M : MultitapeTM) (base : (machine M).Cfg)
    (c : (storage M).Cfg) : (machine M).Cfg where
  state := c.state
  cells := fun j => if hj : j.val = 0 then base.cells j else c.cells (hostToWork j)
  head := fun j => if hj : j.val = 0 then base.head j else c.head (hostToWork j)

theorem step (M : MultitapeTM) (base : (machine M).Cfg) (c : (storage M).Cfg) :
    (machine M).step (embed M base c) = embed M base ((storage M).step c) := by
  cases c
  apply cfg_ext (machine M)
  · rfl
  · funext j p
    fin_cases j <;>
      simp [MultitapeTM.step, machine, controller, transition, embed, workTape,
        hostToWork, workTape_hostToWork]
  · funext j
    fin_cases j <;>
      simp [MultitapeTM.step, machine, controller, transition, embed, workTape,
        hostToWork, workTape_hostToWork]

theorem run (M : MultitapeTM) (base : (machine M).Cfg)
    (c : (storage M).Cfg) (t : ℕ) :
    (machine M).step^[t] (embed M base c) =
      embed M base ((storage M).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', step]

end BitDFT.CountedBlockOnMultiplierAlphabet
end


