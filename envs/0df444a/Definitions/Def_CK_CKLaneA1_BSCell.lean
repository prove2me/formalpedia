-- Prove2me | Definitions.Def_CK_CKLaneA1_BSCell
-- name    : CK_CKLaneA1_BSCell
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:19:24.2712+00:00
-- url     : https://prove2.me/theorems/5efc798b-ee20-463b-b39e-4383743be06e
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSCell` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSCell` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSCell` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSCell (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSCell.lean)

import Definitions.Def_CK_CKLaneA1_BSStrip

/-!
# CKLaneA1.BSCell — both-small cell atoms and the cell check
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates
open GeneralCK.Certificates.Reflection (biasE biasB)

def bsR (A B : RNode) : DI := Iv.mk A.ra B.ra
def bsU (s : BSStrip) (A B : RNode) : DI :=
  Iv.mk ((Iv.pt A.ra).mul (Iv.pt s.w1.xa)).lo ((Iv.pt B.ra).mul (Iv.pt s.w2.xa)).hi
def bsSh (A B : RNode) : DI := Iv.mk (SCz - B.ra) (SCz - A.ra)
def bsY (s : BSStrip) (A B : RNode) : DI :=
  Iv.mk (((Iv.pt s.w1.xa).mul (Iv.pt (SCz - B.ra))).mul (Iv.one.sub (Iv.pt s.w1.xa)).recip).lo
    (((Iv.pt s.w2.xa).mul (Iv.pt (SCz - A.ra))).mul (Iv.one.sub (Iv.pt s.w2.xa)).recip).hi
def bsL1y (Y : DI) : DI := Iv.mk ((Iv.pt Y.lo).mul (Iv.one.add (Iv.pt Y.lo)).recip).lo Y.hi
def bsDlo (n : ℕ) (L2 : DI) (B : RNode) (Y : DI) : ℤ := ((rlog n L2 B).neg.add (bsL1y Y)).lo
def bsDhi (n : ℕ) (L2 : DI) (A : RNode) (Y : DI) : ℤ := ((rlog n L2 A).neg.add (bsL1y Y)).hi
def bsD (n : ℕ) (L2 : DI) (A B : RNode) (Y : DI) : DI := Iv.mk (bsDlo n L2 B Y) (bsDhi n L2 A Y)
def bsRd (n : ℕ) (L2 : DI) (A B : RNode) (Y : DI) : DI :=
  if A.ra = 0 then Iv.mk 0 ((Iv.pt B.ra).mul ((rlog n L2 B).neg.add (Iv.pt Y.hi))).hi
  else (bsR A B).mul (bsD n L2 A B Y)
def bsTau (P D : DI) (A : RNode) (dlo : ℤ) : DI :=
  if A.ra = 0 then Iv.mk 0 (Iv.one.add (P.mul (Iv.pt dlo))).recip.hi
  else (Iv.one.add (P.mul D)).recip

def bsSigLoA (Tau : DI) (w1a : ℤ) : ℤ := (Tau.mul (Iv.one.sub (Iv.pt w1a)).recip).lo
def bsSigLoB (Sh P : DI) (dlo : ℤ) : ℤ :=
  (((Iv.pt dlo).mul (Iv.one.add ((Iv.pt P.hi).mul (Iv.pt dlo))).recip).mul (Iv.pt Sh.hi).recip).lo
def bsSigLo (Tau Sh P : DI) (w1a dlo : ℤ) (B : RNode) : ℤ :=
  if B.ra < SCz then max (bsSigLoA Tau w1a) (bsSigLoB Sh P dlo) else bsSigLoA Tau w1a

def bsSigHiA (Tau U : DI) (A : RNode) : ℤ := (Tau.mul ((Iv.pt A.ra).mul (Iv.one.sub (Iv.pt U.hi))).recip).hi
def bsSigHiB0 (Sh P : DI) : ℤ := (((Iv.pt P.lo).recip).mul (Iv.pt Sh.lo).recip).hi
def bsSigHiB1 (Sh P : DI) (dhi : ℤ) : ℤ :=
  (((Iv.pt dhi).mul (Iv.one.add ((Iv.pt P.lo).mul (Iv.pt dhi))).recip).mul (Iv.pt Sh.lo).recip).hi

/-- Upper bound for `σ`, when available. -/
def bsSigHi (Tau Sh P U : DI) (A B : RNode) (dhi : ℤ) : Option ℤ :=
  if A.ra = 0 then
    (if B.ra < SCz ∧ 0 < P.lo then some (bsSigHiB0 Sh P) else none)
  else
    (if B.ra < SCz then some (min (bsSigHiA Tau U A) (bsSigHiB1 Sh P dhi))
     else some (bsSigHiA Tau U A))

def bsNu (sigLo : ℤ) (sigHi : Option ℤ) : DI :=
  Iv.mk (match sigHi with | some h => (Iv.one.add (Iv.pt h)).recip.lo | none => 0)
    (Iv.one.add (Iv.pt sigLo)).recip.hi

def bsQjhA (R U : DI) (w1a : ℤ) : DI :=
  Iv.mk (-SCz) (((R.mul (Iv.one.sub U)).mul (Iv.one.sub (Iv.pt w1a)).recip).neg).hi
def bsQjhB (U Sh Rd : DI) : DI := (((Iv.one.sub U).mul Rd).mul Sh.recip).neg
def bsQjh (R U Sh Rd : DI) (w1a : ℤ) (B : RNode) : DI :=
  if B.ra < SCz then Iv.meet (bsQjhA R U w1a) (bsQjhB U Sh Rd) else bsQjhA R U w1a

/-- All interval atoms of a both-small cell. -/
structure BSAt where
  P : DI
  Om : DI
  W : DI
  Lw : DI
  R : DI
  U : DI
  Sh : DI
  Y : DI
  dlo : ℤ
  dhi : ℤ
  D : DI
  Rd : DI
  Tau : DI
  Rt : DI
  Qu : DI
  Qw : DI
  Kh : DI
  Au : DI
  Sp : DI
  Qjh : DI
  sLo : ℤ
  sHi : Option ℤ
  Nu : DI
  Nus : DI
  IY : DI
  Ylo : ℤ

def bsAt (n : ℕ) (L2 : DI) (s : BSStrip) (A B : RNode) : BSAt :=
  let P := bsP n L2 s
  let R := bsR A B
  let U := bsU s A B
  let Sh := bsSh A B
  let Y := bsY s A B
  let dlo := bsDlo n L2 B Y
  let dhi := bsDhi n L2 A Y
  let D := bsD n L2 A B Y
  let Rd := bsRd n L2 A B Y
  let Tau := bsTau P D A dlo
  let Rt := R.add (P.mul Rd)
  let Au := Iv.mk A.ra (R.mul (Iv.one.sub U).recip).hi
  let Sp := (Rt.add Iv.one).add (P.mul (Au.add (bsLw s)))
  let sLo := bsSigLo Tau Sh P s.w1.xa dlo B
  let sHi := bsSigHi Tau Sh P U A B dhi
  let Nu := bsNu sLo sHi
  { P := P, Om := bsOm n L2 s, W := bsW s, Lw := bsLw s, R := R, U := U, Sh := Sh, Y := Y,
    dlo := dlo, dhi := dhi, D := D, Rd := Rd, Tau := Tau, Rt := Rt,
    Qu := R.mul (Iv.one.sub U), Qw := Iv.one.sub (bsW s), Kh := (Iv.one.sub U).mul Rt,
    Au := Au, Sp := Sp, Qjh := bsQjh R U Sh Rd s.w1.xa B, sLo := sLo, sHi := sHi,
    Nu := Nu, Nus := Iv.one.sub Nu, IY := Sp.mul (Iv.two.mul (P.mul Sh)).recip,
    Ylo := ((Iv.pt Sp.lo).mul (Iv.two.mul ((Iv.pt P.hi).mul (Iv.pt Sh.hi))).recip).lo }

def sHiOK : Option ℤ → Bool
  | some h => decide (0 < (Iv.one.add (Iv.pt h)).lo)
  | none => true

/-- Recip-positivity and sign guards of a cell (everything but the final signs). -/
def bsGuards (s : BSStrip) (A B : RNode) (two : Bool) (a : BSAt) : Bool :=
  decide (0 ≤ A.ra ∧ 0 ≤ a.P.lo ∧ A.ra < B.ra ∧ (A.ra = 0 → 4 * B.ra ≤ SCz) ∧ 0 ≤ a.Y.lo ∧
    0 ≤ a.dlo ∧
    0 < (Iv.one.sub (Iv.pt s.w1.xa)).lo ∧ 0 < (Iv.one.sub (Iv.pt s.w2.xa)).lo ∧
    0 < (Iv.one.add (Iv.pt a.Y.lo)).lo ∧ 0 < (Iv.one.sub a.U).lo ∧ 0 < a.Sp.lo ∧ 0 ≤ a.sLo ∧
    0 < (Iv.one.add (Iv.pt a.sLo)).lo ∧
    (A.ra = 0 → 0 < (Iv.one.add (a.P.mul (Iv.pt a.dlo))).lo) ∧
    (A.ra ≠ 0 → 0 < (Iv.one.add (a.P.mul a.D)).lo ∧
      0 < ((Iv.pt A.ra).mul (Iv.one.sub (Iv.pt a.U.hi))).lo) ∧
    (B.ra < SCz → 0 < a.Sh.lo ∧ 0 < (Iv.pt a.Sh.hi).lo ∧ 0 < (Iv.pt a.Sh.lo).lo ∧
      0 < (Iv.one.add ((Iv.pt a.P.hi).mul (Iv.pt a.dlo))).lo ∧
      (A.ra ≠ 0 → 0 < (Iv.one.add ((Iv.pt a.P.lo).mul (Iv.pt a.dhi))).lo)) ∧
    (two = true → 0 < (Iv.two.mul (a.P.mul a.Sh)).lo) ∧
    (two = false → 0 < (Iv.two.mul ((Iv.pt a.P.hi).mul (Iv.pt a.Sh.hi))).lo)) &&
  sHiOK a.sHi

/-- Final sign check of a cell, given its contact data. -/
def bsFinal (n : ℕ) (L2 : DI) (a : BSAt) (cd : CData) : Bool :=
  let C := cC cd
  let E := cE n L2 cd
  let Bb := cB n L2 cd
  let FoC := cFoC (cLoC n cd) E Bb C
  let F := C.mul FoC
  let Rh := FoC.mul ((Iv.two.mul E).mul a.Sp.recip)
  let Wh := (cG E Bb C).mul a.Sp.recip
  let Hh := Iv.one.sub (Iv.two.mul a.U)
  let Hms := Hh.sub (a.W.mul a.Sh)
  let cc := bsCIv a.Tau a.P a.Om a.Qu a.Qw a.Sh a.Sp a.Kh a.Qjh a.Nu a.Nus Rh Wh Hh Hms
  let mm := bsMIv a.Tau a.P a.Qu a.Sh a.Sp a.Kh F Wh Hh
  decide (0 < (Iv.one.sub ((Iv.pt cd.chi).mul (Iv.pt cd.chi))).lo ∧
    0 < ((Iv.one.sub (C.mul C)).mul Bb).lo ∧
    0 < (((Iv.one.sub (C.mul C)).mul (Iv.one.sub (C.mul C))).mul ((Bb.mul Bb).mul Bb)).lo ∧
    0 < cc.lo ∧ 0 < mm.lo)

/-- The both-small cell check. -/
def bsCellCheck (n : ℕ) (L2 : DI) (s : BSStrip) (A B : RNode) (two : Bool) (cd : CData) : Bool :=
  let a := bsAt n L2 s A B
  rnodeOK B && (decide (A.ra = 0) || rnodeOK A) && bsGuards s A B two a &&
    bsBracketOK n L2 two a.IY a.Ylo cd && bsFinal n L2 a cd

end CKLaneA1


