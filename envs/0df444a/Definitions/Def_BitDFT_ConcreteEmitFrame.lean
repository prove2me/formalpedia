-- Prove2me | Definitions.Def_BitDFT_ConcreteEmitFrame
-- name    : BitDFT_ConcreteEmitFrame
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T08:09:15.959454+00:00
-- url     : https://prove2.me/theorems/c41a4e82-5349-4c6c-b75b-ef5fa131ec47
-- title:
--   Align the multiplier frame with the serializer emit phase
-- statement:
--   Suppose a multiplier controller has left its product source on tape 1 with the required bit string and head position. Then the shared-host serializer can be initialized in its emit phase so that the product tape, parked multiplier tapes, output prefix, countdown, and template occupy exactly the routed frame required by the counted-block serializer.
-- source:
--   The frame is assembled by placing the multiplier input on the host input tape, mapping the product source through the accepted alphabet embedding, parking each old multiplier tape in its routed extension slot, and initializing the three appended serializer tapes from the counted-block emit frame.

import Definitions.Def_BitDFT_SerializerEmitContinuation
import Theorems.Thm_BitDFT_serializer_fresh_routing_old_tapes

set_option autoImplicit false
noncomputable section
namespace BitDFT.RoutedCountedBlockFreshTapes
open IntMul BitDFT.MachineSequence

def parkedCells (M : MultitapeTM) (cells : Fin (source M).k → ℕ → (source M).Sym) :
    Fin (extension M).k → ℕ → (source M).Sym := fun j p =>
  if h : 5 ≤ j.val then cells ⟨j.val - 3, by
    have hj := j.isLt
    dsimp [extension, host, CountedBlockOnMultiplierAlphabet.host,
      TapeExtension.machine] at hj ⊢
    omega
  ⟩ p else (source M).blank

def parkedHeads (M : MultitapeTM) (heads : Fin (source M).k → ℕ) :
    Fin (extension M).k → ℕ := fun j =>
  if h : 5 ≤ j.val then heads ⟨j.val - 3, by
    have hj := j.isLt
    dsimp [extension, host, CountedBlockOnMultiplierAlphabet.host,
      TapeExtension.machine] at hj ⊢
    omega
  ⟩ else 0

def emitFrame (M : MultitapeTM) (base : (host M).Cfg)
    (oldCells : Fin (extension M).k → ℕ → (source M).Sym)
    (oldHeads : Fin (extension M).k → ℕ) (pre out x y : List Bool) :
    (serializerEmitContinuation M).machine.Cfg :=
  { state := CountedStream.State.emit
    cells := (embed M base oldCells oldHeads
      (AlphabetEmbedding.embed
        (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
        (CountedBlock.frame pre out x y y.reverse 0 .emit))).cells
    head := (embed M base oldCells oldHeads
      (AlphabetEmbedding.embed
        (CountedBlockOnMultiplierAlphabet.alphabetMap (source M))
        (CountedBlock.frame pre out x y y.reverse 0 .emit))).head }

def emitHostBase (M : MultitapeTM) {C : Controller (source M)}
    (cEnd : C.machine.Cfg) : (host M).Cfg :=
  ⟨(host M).qStart,
    (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
      dsimp [source, IntMul.TrackedOutputShift.machine]; omega
    ⟩ p else (host M).blank),
    (fun i => if i.val = 0 then cEnd.head ⟨0, by
      dsimp [source, IntMul.TrackedOutputShift.machine]; omega
    ⟩ else 0)⟩

def castSerializerCfg (M : MultitapeTM) (c : (machine M).Cfg) :
    (serializerEmitContinuation M).machine.Cfg :=
  ⟨c.state, c.cells, c.head⟩

private theorem cfgExt (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem countedTapeEmbed (M : MultitapeTM) (w : List TapeCopy.Sym) :
    (fun p => PreprocessorAlphabet.encode (source M)
      (CountedStream.machine.tapeOf w p)) =
      (source M).tapeOf (w.map (PreprocessorAlphabet.encode (source M))) := by
  funext p
  cases p with
  | zero => rfl
  | succ p =>
      simp only [IntMul.MultitapeTM.tapeOf, List.getD_eq_getElem?_getD,
        List.getElem?_map]
      cases w[p]? <;> simp [PreprocessorAlphabet.encode]

private theorem countedBitsEmbed (M : MultitapeTM) (w : List Bool) :
    (w.map CountedStream.machine.bitSym).map
      (PreprocessorAlphabet.encode (source M)) =
      w.map (source M).bitSym := by
  rw [List.map_map]
  congr 1
  funext b
  cases b <;> rfl

/-- Choose the continuation's appended tapes from the routed serializer frame,
    and park each old source tape in the accepted `i+3` logical slot. -/
theorem concrete_emit_frame (M : MultitapeTM) (C : Controller (source M))
    (cEnd : C.machine.Cfg) (pre out x y : List Bool)
    (hProductCells : cEnd.cells ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      (host M).tapeOf ((pre ++ x).map (host M).bitSym))
    (hProductHead : cEnd.head ⟨1, by dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ =
      pre.length + 1) :
    MachineSequence.handoff (suffixControllerOnSerializerHost M C)
      (serializerEmitContinuation M)
      (suffixEmbed M C
        (fun j p => if j.val < (source M).k then (source M).blank else
          (emitFrame M
            ⟨(host M).qStart,
              (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
              (fun i => if i.val = 0 then cEnd.head ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
            (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).cells j p)
        (fun j => if j.val < (source M).k then 0 else
          (emitFrame M
            ⟨(host M).qStart,
              (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
              (fun i => if i.val = 0 then cEnd.head ⟨0, by
                dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
            (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).head j)
        cEnd) =
    ⟨CountedStream.State.emit,
        (emitFrame M
          ⟨(host M).qStart,
            (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
            (fun i => if i.val = 0 then cEnd.head ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
          (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).cells,
        (emitFrame M
          ⟨(host M).qStart,
            (fun i p => if i.val = 0 then cEnd.cells ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ p else (host M).blank),
            (fun i => if i.val = 0 then cEnd.head ⟨0, by
              dsimp [source, IntMul.TrackedOutputShift.machine]; omega⟩ else 0)⟩
          (parkedCells M cEnd.cells) (parkedHeads M cEnd.head) pre out x y).head⟩ := by
  apply cfgExt (serializerEmitContinuation M).machine
  · rfl
  · funext i p
    by_cases hi : i.val < (source M).k
    · by_cases h0 : i.val = 0
      · have heq : i = ⟨0, by have hk := (source M).two_le_k; omega⟩ := Fin.ext h0
        rw [heq]
        let r := M.k + 2 - 2
        let e := SerializerFreshTapeRouting.routing r
        have hz : e.symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
          apply e.injective
          rw [e.apply_symm_apply]
          exact (SerializerFreshTapeRouting.routing_input r).symm
        have hzTarget :
            (SerializerFreshTapeRouting.routing (M.k + 2 - 2)).symm
              (⟨0, by omega⟩ : Fin (5 + (M.k + 2 - 2))) = ⟨0, by omega⟩ := by
          simpa [e, r] using hz
        simp only [MachineSequence.handoff, suffixEmbed, emitFrame,
          RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
          TapeExtension.embed]
        rw [hzTarget]
        simp [CountedBlockOnMultiplierAlphabet.embed]
      · by_cases h1 : i.val = 1
        · have heq : i = ⟨1, by have hk := (source M).two_le_k; omega⟩ := Fin.ext h1
          rw [heq]
          let r := M.k + 2 - 2
          let e := SerializerFreshTapeRouting.routing r
          have hp : e.symm ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
            apply e.injective
            rw [e.apply_symm_apply]
            exact (SerializerFreshTapeRouting.routing_product r).symm
          have hpTarget :
              (SerializerFreshTapeRouting.routing (M.k + 2 - 2)).symm
                (⟨1, by omega⟩ : Fin (5 + (M.k + 2 - 2))) = ⟨1, by omega⟩ := by
            simpa [e, r] using hp
          simp only [MachineSequence.handoff, suffixEmbed, emitFrame,
            RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
            TapeExtension.embed]
          rw [hpTarget]
          have h1M : 1 < M.k + 2 := by have hk := M.two_le_k; omega
          simp only [CountedBlockOnMultiplierAlphabet.embed, CountedBlock.frame,
            AlphabetEmbedding.embed, CountedBlockOnMultiplierAlphabet.alphabetMap,
            PreprocessorAlphabet.alphabetMap, CountedBlockOnMultiplierAlphabet.hostToWork,
            h1M]
          calc
            cEnd.cells 1 p = (host M).tapeOf ((pre ++ x).map (host M).bitSym) p := by
              simpa using congrFun hProductCells p
            _ = (PreprocessorAlphabet.alphabetMap (source M)).encode
                ((CountedStream.machine.tapeOf
                  ((pre ++ x).map CountedStream.machine.bitSym)) p) := by
              have hSymbols := countedBitsEmbed M (pre ++ x)
              have hTape := congrFun (countedTapeEmbed M
                ((pre ++ x).map CountedStream.machine.bitSym)) p
              rw [hSymbols] at hTape
              change (source M).tapeOf ((pre ++ x).map (source M).bitSym) p =
                PreprocessorAlphabet.encode (source M)
                  (CountedStream.machine.tapeOf
                    ((pre ++ x).map CountedStream.machine.bitSym) p)
              exact hTape.symm
        · have hi2 : 2 ≤ i.val := by omega
          let r := M.k + 2 - 2
          let e := SerializerFreshTapeRouting.routing r
          have hbound : i.val < r + 2 := by
            dsimp [r, source, IntMul.TrackedOutputShift.machine] at hi
            omega
          have holdRoute : e.symm i = ⟨i.val + 3, by
              have hk := (source M).two_le_k
              dsimp [r, source, IntMul.TrackedOutputShift.machine]
              omega⟩ := by
            apply e.injective
            rw [e.apply_symm_apply]
            exact (BitDFT.serializer_fresh_routing_old_tapes r
              ⟨i.val, hbound⟩ hi2).symm
          have hbig : 5 ≤ (e.symm i).val := by
            simp only [holdRoute]
            omega
          have hiM : i.val < M.k + 2 := by
            simpa [source, IntMul.TrackedOutputShift.machine] using hi
          simp only [MachineSequence.handoff, suffixEmbed, emitFrame,
            RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
            TapeExtension.embed]
          rw [holdRoute]
          have hge : ¬ i.val + 3 < 5 := by omega
          simp only [dif_pos hiM, dif_neg hge, parkedCells,
            dif_pos (by omega : 5 ≤ i.val + 3)]
          congr 1
    · have hi' : ¬ i.val < M.k + 2 := by
        simpa [source, IntMul.TrackedOutputShift.machine] using hi
      simp [MachineSequence.handoff, suffixEmbed, emitFrame, hi',
        RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
        TapeExtension.embed, CountedBlockOnMultiplierAlphabet.embed]
  · funext i
    by_cases hi : i.val < (source M).k
    · by_cases h0 : i.val = 0
      · have heq : i = ⟨0, by have hk := (source M).two_le_k; omega⟩ := Fin.ext h0
        rw [heq]
        let r := M.k + 2 - 2
        let e := SerializerFreshTapeRouting.routing r
        have hz : e.symm ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
          apply e.injective
          rw [e.apply_symm_apply]
          exact (SerializerFreshTapeRouting.routing_input r).symm
        have hzTarget :
            (SerializerFreshTapeRouting.routing (M.k + 2 - 2)).symm
              (⟨0, by omega⟩ : Fin (5 + (M.k + 2 - 2))) = ⟨0, by omega⟩ := by
          simpa [e, r] using hz
        simp only [MachineSequence.handoff, suffixEmbed, emitFrame,
          RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
          TapeExtension.embed]
        rw [hzTarget]
        simp [CountedBlockOnMultiplierAlphabet.embed]
      · by_cases h1 : i.val = 1
        · have heq : i = ⟨1, by have hk := (source M).two_le_k; omega⟩ := Fin.ext h1
          rw [heq]
          let r := M.k + 2 - 2
          let e := SerializerFreshTapeRouting.routing r
          have hp : e.symm ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
            apply e.injective
            rw [e.apply_symm_apply]
            exact (SerializerFreshTapeRouting.routing_product r).symm
          have hpTarget :
              (SerializerFreshTapeRouting.routing (M.k + 2 - 2)).symm
                (⟨1, by omega⟩ : Fin (5 + (M.k + 2 - 2))) = ⟨1, by omega⟩ := by
            simpa [e, r] using hp
          simp only [MachineSequence.handoff, suffixEmbed, emitFrame,
            RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
            TapeExtension.embed]
          rw [hpTarget]
          simp only [CountedBlockOnMultiplierAlphabet.embed, CountedBlock.frame,
            AlphabetEmbedding.embed, CountedBlockOnMultiplierAlphabet.alphabetMap,
            PreprocessorAlphabet.alphabetMap, CountedBlockOnMultiplierAlphabet.hostToWork]
          simpa [host, CountedBlockOnMultiplierAlphabet.host,
            CountedBlockOnMultiplierAlphabet.machine,
            IntMul.TrackedOutputShift.machine] using hProductHead
        · have hi2 : 2 ≤ i.val := by omega
          let r := M.k + 2 - 2
          let e := SerializerFreshTapeRouting.routing r
          have hbound : i.val < r + 2 := by
            dsimp [r, source, IntMul.TrackedOutputShift.machine] at hi
            omega
          have holdRoute : e.symm i = ⟨i.val + 3, by
              have hk := (source M).two_le_k
              dsimp [r, source, IntMul.TrackedOutputShift.machine]
              omega⟩ := by
            apply e.injective
            rw [e.apply_symm_apply]
            exact (BitDFT.serializer_fresh_routing_old_tapes r
              ⟨i.val, hbound⟩ hi2).symm
          have hiM : i.val < M.k + 2 := by
            simpa [source, IntMul.TrackedOutputShift.machine] using hi
          simp only [MachineSequence.handoff, suffixEmbed, emitFrame,
            RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
            TapeExtension.embed]
          rw [holdRoute]
          have hge : ¬ i.val + 3 < 5 := by omega
          simp only [dif_pos hiM, dif_neg hge, parkedHeads,
            dif_pos (by omega : 5 ≤ i.val + 3)]
          congr 1
    · have hi' : ¬ i.val < M.k + 2 := by
        simpa [source, IntMul.TrackedOutputShift.machine] using hi
      simp [MachineSequence.handoff, suffixEmbed, emitFrame, hi',
        RoutedCountedBlockFreshTapes.embed, TapePermutation.embed,
        TapeExtension.embed, CountedBlockOnMultiplierAlphabet.embed]

end BitDFT.RoutedCountedBlockFreshTapes
end


