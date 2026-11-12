-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Framework
-- name    : CatalyticTreeEval_Main_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:30:33.559192+00:00
-- url     : https://prove2.me/theorems/ae9d2ab6-1834-401a-8dff-a978e33fad59
-- title:
--   The section-four matching-and-decoding setting
-- statement:
--   A frame records $m,d,\ell,k,s$, a score set $S$, matching vectors $U,V$, and decoder $D$. Validity requires $m>1$, $\ell>0$, $0\in S$, matching scores in $S\setminus\{0\}$ off the diagonal, noncancellation, an $(S+S)$-decoder, and
--
--   $$s\ge\log_2(dm).$$
--
--   Computational access is a separate property, supplied by fixed charged vector and decoder printers with a common constant multiplier of $s$. Only the one-level theorem also receives a charged output-family printer. Parameter strings include $m,d,\ell,k$ in fixed self-delimiting form; one-level input appends the full gate table. The padded dimension is the larger of $d$ and the number of packed label blocks needed in Section 4.3.
--
--   These are the source's framework hypotheses. Neither this frame nor efficient ingredient access is an assumption in the unconditional headline theorem or Corollary 4.7.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Section 4 standing setting; Section 4.3, printed p. 21 (PDF p. 23); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_OracleMachine

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The §4 standing algebraic setting. Computational access is a separate property. -/
structure Frame where
  m : ℕ
  d : ℕ
  l : ℕ
  k : ℕ
  s : ℕ
  S : Set (ZMod m)
  U : Label l → Vec m d
  V : Label l → Vec m d
  D : Decoder m k

def Frame.valid (F : Frame) : Prop :=
  1 < F.m ∧ 0 < F.l ∧ SMatching F.S F.U F.V ∧ Noncancelling F.S ∧
    IsDecoder (sumset F.S) F.D ∧ log₂ (F.d * F.m) ≤ F.s

def Frame.params (a : List Bool) (F : Frame) : List Bool :=
  listCode a ++ natsCode [F.m,F.d,F.l,F.k]

def Frame.access (F : Frame) (a : List Bool) (MV MD : Machine) (C : ℝ) : Prop :=
  VectorAccess MV (F.params a) F.U F.V (C * F.s) ∧
    DecoderAccess MD (F.params a) F.D (C * F.s)

def OutputAccess (F : Frame) (W : Label F.l → Vec F.m F.d)
    (a : List Bool) (MW : Machine) (C : ℝ) : Prop :=
  ∀ y, Prints MW (listCode (F.params a) ++ natCode y.val) (vecCode (W y)) (C * F.s)

def oneLevelInput (F : Frame) (a : List Bool)
    (f : Label F.l → Label F.l → Label F.l) : List Bool :=
  listCode (F.params a) ++ tableCode f

/-- Zero padding used in §4.3, including room for the full label, not only one decision bit. -/
def paddedDimension (F : Frame) : ℕ :=
  max F.d ((F.l + Nat.log 2 F.m - 1) / Nat.log 2 F.m)

end CatalyticTreeEval.Main


