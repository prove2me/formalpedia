-- Prove2me | Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
-- name    : BitDFT_ReaderHostFrame_WorkSupport_v2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T18:08:22.197565+00:00
-- url     : https://prove2.me/theorems/66096e40-0f2a-449e-9d58-7a0cbb3f7ec2
-- title:
--   Shared-host reader frame support lemmas (v2)
-- statement:
--   Auxiliary constructions and proved routing lemmas for embedding the Fourier and header-reader configurations into the common tracked-multiplier host. These support the work-bank initialization theorem.
-- source:
--   Shared helper declarations extracted from the reader-frame proof, with a single import used by both target and solution.

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_component_tape
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_extra_tape
import Theorems.Thm_BitDFT_header_inverse_fourier_bank
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

abbrev tracked (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev host (A M H : MultitapeTM) := BankedTripleAlphabetHost.multiplierMachine A (tracked M) H

def multiplierTapeRoute (A M H : MultitapeTM) (i : Fin (tracked M).k) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) := by
  let X := tracked M
  have hX : X.k ≤ DedicatedTapeBanks.width A X H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k
    have hX := X.two_le_k
    have hH := H.two_le_k
    omega
  let r := DedicatedTapeBanks.width A X H - X.k
  let h : X.k + r = DedicatedTapeBanks.width A X H := Nat.add_sub_of_le hX
  exact BankedTripleAlphabetHost.route A X H
    (DedicatedTapeBanks.multiplierOffset A X H)
    (by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.multiplierOffset, DedicatedTapeBanks.tail]
      omega)
    (Fin.cast h (TapeExtension.oldTape X r i))

def fourierRoute (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.route A (tracked M) H
    (DedicatedTapeBanks.fourierOffset A (tracked M) H)
    (by have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.fourierOffset, DedicatedTapeBanks.tail]; omega)

def headerRoute (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.route A (tracked M) H
    (DedicatedTapeBanks.headerOffset A (tracked M) H)
    (by have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]; omega)

def parkedCells (A M H : MultitapeTM) (cF : A.Cfg) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) → ℕ →
      (BankedTripleAlphabetHost.carrier A (tracked M) H).Sym := by
  let R := fourierRoute A M H
  exact fun p x =>
    let j := R.symm p
    if hj : j.val < A.k then
      (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells ⟨j.val, hj⟩ x)
    else if x = 0 then (BankedTripleAlphabetHost.carrier A (tracked M) H).startSym
      else (BankedTripleAlphabetHost.carrier A (tracked M) H).blank

def parkedHeads (A M H : MultitapeTM) (cF : A.Cfg) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) → ℕ := by
  let R := fourierRoute A M H
  exact fun p =>
    let j := R.symm p
    if hj : j.val < A.k then cF.head ⟨j.val, hj⟩ else 1


theorem hostAlphabet_tape_embed {X Y : MultitapeTM}
    (e : AlphabetEmbedding.Map X Y) (w : List X.Sym) :
    (fun p => e.encode (X.tapeOf w p)) = Y.tapeOf (w.map e.encode) := by
  funext p
  cases p with
  | zero => exact e.marker
  | succ p =>
      simp [MultitapeTM.tapeOf]
      cases h : w[p]? <;> simp [h, e.blank]
theorem header_frame_keeps_fourier_tape (A M H : MultitapeTM)
    (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k) (hj : 1 ≤ j.val)
    (p : Fin (DedicatedTapeBanks.width A (tracked M) H))
    (hp : p.val = j.val) :
    let eH := TripleAlphabet.header A (tracked M) H
    let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
    let hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]; omega
    let hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
      rw [DedicatedTapeBanks.width_eq_sum]
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      omega
    let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
      (parkedCells A M H cF) (parkedHeads A M H cF) cH
    cfg.cells p =
      (fun x => (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells j x)) ∧
    cfg.head p = cF.head j := by
  let eH := TripleAlphabet.header A (tracked M) H
  let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
  have hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
    dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  have hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
    (parkedCells A M H cF) (parkedHeads A M H cF) cH
  let Rh := headerRoute A M H
  let Rf := fourierRoute A M H
  have hpA : j.val < A.k := j.isLt
  have hRF : Rf ⟨j.val, by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.width, DedicatedTapeBanks.tail]; omega⟩ = p := by
    apply Fin.ext
    have haddr := DedicatedTapeBanks.fourier_work_address A (tracked M) H j hj
    have hv := congrArg Fin.val haddr
    simpa [Rf, fourierRoute, BankedTripleAlphabetHost.route,
      DedicatedTapeBanks.fourierOffset] using hv.trans hp.symm
  have hjinv : Rf.symm p = ⟨j.val, by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.width, DedicatedTapeBanks.tail]; omega⟩ := by
    calc
      Rf.symm p = Rf.symm (Rf ⟨j.val, by
        have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
        dsimp [DedicatedTapeBanks.width, DedicatedTapeBanks.tail]; omega⟩) := by rw [hRF]
      _ = _ := Rf.symm_apply_apply _
  have hheaderInv : H.k ≤ (Rh.symm p).val := by
    apply BitDFT.header_inverse_fourier_bank A (tracked M) H p
    · have hppos : 1 ≤ p.val := by omega
      exact hppos
    · have hplt : p.val < A.k := by omega
      exact hplt
  have hExtra := BankedTripleAlphabetHost.config_extra_tape A (tracked M) H H eH hoff hhoff hX
    (parkedCells A M H cF) (parkedHeads A M H cF) cH (Rh.symm p) hheaderInv
  have hrouteBack : Rh ((Rh.symm p)) = p := Rh.apply_symm_apply p
  have hExtra' : cfg.cells (Rh (Rh.symm p)) = parkedCells A M H cF (Rh (Rh.symm p)) ∧
      cfg.head (Rh (Rh.symm p)) = parkedHeads A M H cF (Rh (Rh.symm p)) := by
    simpa [cfg, Rh, headerRoute, hoff] using hExtra
  rw [hrouteBack] at hExtra'
  change cfg.cells p = (fun x => (TripleAlphabet.fourier A (tracked M) H).encode (cF.cells j x)) ∧
    cfg.head p = cF.head j
  constructor
  · simpa [parkedCells, Rf, hjinv, hpA] using hExtra'.1
  · simpa [parkedHeads, Rf, hjinv, hpA] using hExtra'.2


/-- The parsed dimension stays at the host address reserved for the staging
    controller, with the header embedding applied symbol by symbol. -/
theorem header_frame_dimension_projection (A M H : MultitapeTM)
    (hH4 : 3 < H.k) (cF : A.Cfg) (cH : H.Cfg) :
    let eH := TripleAlphabet.header A (tracked M) H
    let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
    let hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]; omega
    let hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
      rw [DedicatedTapeBanks.width_eq_sum]
      have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
      omega
    let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
      (parkedCells A M H cF) (parkedHeads A M H cF) cH
    cfg.cells (BankedOperandStage.dimensionTape A M H) =
      (fun p => eH.encode (cH.cells ⟨3, by
        have hH := hH4
        exact by omega⟩ p)) ∧
    cfg.head (BankedOperandStage.dimensionTape A M H) = cH.head ⟨3, by
      have hH := hH4
      exact by omega⟩ := by
  let eH := TripleAlphabet.header A (tracked M) H
  let hoff := DedicatedTapeBanks.headerOffset A (tracked M) H
  have hhoff : hoff < 4 + DedicatedTapeBanks.tail A (tracked M) H := by
    dsimp [hoff, DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  have hX : H.k ≤ DedicatedTapeBanks.width A (tracked M) H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k; have hM := (tracked M).two_le_k; have hH := H.two_le_k
    omega
  let cfg := BankedTripleAlphabetHost.config A (tracked M) H H eH hoff hhoff hX
    (parkedCells A M H cF) (parkedHeads A M H cF) cH
  let r := DedicatedTapeBanks.width A (tracked M) H - H.k
  let h : H.k + r = DedicatedTapeBanks.width A (tracked M) H := Nat.add_sub_of_le hX
  let j : Fin H.k := ⟨3, by exact hH4⟩
  let logical := Fin.cast h (TapeExtension.oldTape H r j)
  have hcomp := BankedTripleAlphabetHost.config_component_tape A (tracked M) H H eH
    hoff hhoff hX (parkedCells A M H cF) (parkedHeads A M H cF) cH j
  have haddr : headerRoute A M H logical = BankedOperandStage.dimensionTape A M H := by
    apply Fin.ext
    have hv := congrArg Fin.val (DedicatedTapeBanks.header_value_tape_address A (tracked M) H)
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    simp [headerRoute, hoff, logical, j, TapeExtension.oldTape, Fin.cast, BankedTripleAlphabetHost.route,
      DedicatedTapeBanks.headerOffset, DedicatedTapeBanks.tail,
      BankedOperandStage.dimensionTape] at hv ⊢
    omega
  have hcomp' := hcomp
  change cfg.cells (headerRoute A M H logical) =
      (fun p => eH.encode (cH.cells j p)) ∧
    cfg.head (headerRoute A M H logical) = cH.head j at hcomp'
  rw [haddr] at hcomp'
  simpa [cfg, j] using hcomp'


theorem encode_tapeOf_bits {X Y : MultitapeTM}
    (e : BitDFT.AlphabetEmbedding.Map X Y) (w : List Bool) :
    (fun p => e.encode (X.tapeOf (w.map X.bitSym) p)) =
      Y.tapeOf (w.map Y.bitSym) := by
  have hbits : (w.map X.bitSym).map e.encode = w.map Y.bitSym := by
    induction w with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons]
      rw [ih]
      cases b <;> simp [MultitapeTM.bitSym, e.zero, e.one]
  rw [hostAlphabet_tape_embed e (w.map X.bitSym)]
  rw [hbits]


