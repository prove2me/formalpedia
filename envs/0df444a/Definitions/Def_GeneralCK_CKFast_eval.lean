-- Prove2me | Definitions.Def_GeneralCK_CKFast_eval
-- name    : GeneralCK_CKFast_eval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T04:51:33.383426+00:00
-- url     : https://prove2.me/theorems/df76c8ca-90a0-40ed-8844-b31b8c89ce34
-- title:
--   Computing checker for the correction-band jet program (RB1/RB2)
-- statement:
--   A **computing** interval evaluator for the 136-step correction jet program used by the correction-band certificates of the general Courtade–Kumar proof. The program has the shapes of `GeneralCK.Certificates.CorrectionFactorizedProgramKernel.kernelProgram`, and its outputs 14 and 0 are the natural correction quantities $m_{11}(u,w)$ and $k_{\det}(u,w)$, where $w = u + \rho(1/2-u)$.
--
--   The source certificates store every intermediate `DyadicBivariateJetEnclosure` as literal data and only *check* each one. Here the enclosures are *computed* from the input box by exact integer arithmetic at scale $2^{40}$:
--
--   - **Arithmetic steps.** Add, negate, multiply, invert and log steps use the library's own interval jet operations. Logarithms use the library's atanh series at scale $2^{64}$ (`DyadicLogSeries.enclosure`, 16 terms), with $\log 2$ precomputed.
--   - **Contact step.** The reflection-contact step uses the library enclosure `DyadicContact.enclosure c B`. Its bracket $c$ is supplied by the certificate and checked by the endpoint entropy tests of `ProvedTranscendental.contact_bracket`. $B$ is computed.
--   - **Cells and covers.** `cellOK` runs the program once at the center of a box $[U_0/D, U_1/D]\times[R_0/D, R_1/D]$ with $D = 50\cdot 2^{24}$, and once on the whole box. It then tests the second-order Taylor lower bound of both outputs in exact integer form (`taylorZ` equals $8D^2 2^{40}$ times `BivariateJetEnclosure.taylorLower`). `treeOK` checks a guillotine subdivision of a box by such cells.
--
--   Everything is executable, so certificates are discharged by `decide +kernel`. Each cell needs only its box and two contact brackets as data. Soundness is the theorem `GeneralCK.CKFast.tree_sound`.
--
--   Mathematics and the original certificate design: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931. Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean.
-- source:
--   Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (2026); certificate program: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/REVIEW_GUIDE.md (section 4, R-B1/R-B2 families)

import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

/-!
# Computing evaluator for the correction-band jet program

Instead of storing every intermediate `DyadicBivariateJetEnclosure` of the
136-step correction program as literal certificate data (as each RB1/RB2 cell
of the source development does), this file computes all of them — including
the logarithm enclosures and the reflection-contact enclosure — from the input
box and a two-integer contact bracket.  Everything is integer arithmetic, so the
kernel runs it inside `decide`.

Mathematics and the original certificate design: Z. Chen, A. Gohari,
A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most
Informative Boolean Function Conjecture*, arXiv:2609.24931; Lean development
https://github.com/dpwoodru/general-courtade-kumar-lean.
-/

namespace GeneralCK.CKFast
open GeneralCK.Certificates GeneralCK.Certificates.DyadicInterval
open GeneralCK.Certificates.BivariateJetProgram

abbrev DI := DyadicInterval 40
abbrev Enc := DyadicBivariateJetEnclosure 40

/-- `2^40`, the fixed scale of the certificates. -/
def S : ℤ := 1099511627776
/-- `2^24`, the gap between the working scale 40 and the log-series scale 64. -/
def S24 : ℤ := 16777216
/-- Number of odd atanh-series terms (as in the source certificates). -/
def nTerms : ℕ := 16

/-! ## Logarithms -/

/-- `log 2` series enclosure at scale 64 (`= enclosure (fraction 64 1 3) 16`). -/
def ln2E : DyadicInterval 64 := ⟨12786308645202655420, 12786308645202662926⟩

/-- `DyadicFastLog.approximation 64 a b e nTerms` with the `log 2` series precomputed. -/
def approx (a b : ℤ) (e : ℕ) : DyadicInterval 64 :=
  (((ofInt 64 e).mul ln2E).add
    (DyadicLogSeries.enclosure (DyadicFastLog.reduced 64 a b e) nTerms)).neg

/-- Reduction exponent `e = ⌊log₂ (b / a)⌋`. -/
def redExp (a b : ℤ) : ℕ := Nat.log2 (b / a).toNat

/-- The cheap part of `DyadicFastLog.check`: positivity and the series guard. -/
def guardOK (a b : ℤ) (e : ℕ) : Bool :=
  decide (0 < a ∧ 0 < b) && DyadicLogSeries.guard (DyadicFastLog.reduced 64 a b e)

/-- Enclosure (scale 40) of `log (z / 2^40)`. -/
def logPt (z : ℤ) : DI :=
  if z ≤ S then
    let I := approx z S (redExp z S)
    ⟨floorDiv I.lo S24, ceilDiv I.hi S24⟩
  else
    let I := approx S z (redExp S z)
    ⟨floorDiv (-I.hi) S24, ceilDiv (-I.lo) S24⟩

def logPtOK (z : ℤ) : Bool :=
  if z ≤ S then guardOK z S (redExp z S) else guardOK S z (redExp S z)

/-- Log enclosure of a positive interval: hull of the endpoint enclosures. -/
def logIv (b : DI) : DI :=
  let l := logPt b.lo
  let h := logPt b.hi
  ⟨min l.lo h.lo, max l.hi h.hi⟩

def logIvOK (b : DI) : Bool := decide (0 < b.lo) && logPtOK b.lo && logPtOK b.hi

/-- `log 2` at scale 40. -/
def two : DI := logPt (2 * S)

/-! ## Reflection contact -/

def onePlus (c : ℤ) : DI := (ofInt 40 1).add (DyadicContact.point c)
def oneMinus (c : ℤ) : DI := (ofInt 40 1).sub (DyadicContact.point c)

/-- Enclosure of `biasE (c / 2^40)` at a point `c`. -/
def biasEPt (c : ℤ) : DI :=
  ProvedTranscendental.entropyRaw (DyadicContact.point c) two (logIv (onePlus c)) (logIv (oneMinus c))

def biasEPtOK (c : ℤ) : Bool := logIvOK (onePlus c) && logIvOK (oneMinus c)

def leftOK (Y : DI) (c : ℤ) : Bool := decide ((Y.mul (DyadicContact.point c)).hi ≤ (biasEPt c).lo)
def rightOK (Y : DI) (c : ℤ) : Bool := decide ((biasEPt c).hi ≤ (Y.mul (DyadicContact.point c)).lo)

def contactB (c : DI) : DI :=
  ProvedTranscendental.denominatorRaw two (logIv (DyadicContact.gap c))

/-- Every hypothesis of `contact_bracket` / `contact_jet` that is a computation. -/
def contactOK (Y c : DI) : Bool :=
  decide (0 < Y.lo) && decide (0 ≤ c.lo) && decide (c.hi ≤ S) && decide (c.lo ≤ c.hi) &&
  biasEPtOK c.lo && biasEPtOK c.hi && leftOK Y c.lo && rightOK Y c.hi &&
  logPtOK (2 * S) && logIvOK (DyadicContact.gap c) &&
  decide (0 < (contactB c).lo) && decide (0 < (DyadicContact.gap c).lo)

/-! ## The program -/

def zeroE : Enc := zeroBox 40

/-- One computed step; `none` if a side condition fails. `h` is the contact bracket. -/
def step (h : DI) (s : Shape) (boxes : List Enc) : Option Enc :=
  if BivariateProvedProgram.InRange s boxes.length then
    match s with
    | .add i j => some ((boxes.getD i zeroE).add (boxes.getD j zeroE))
    | .neg i => some (boxes.getD i zeroE).neg
    | .mul i j => some ((boxes.getD i zeroE).mul (boxes.getD j zeroE))
    | .inv i =>
        let b := boxes.getD i zeroE
        if b.value.positiveCheck then some b.inv else none
    | .log i =>
        let b := boxes.getD i zeroE
        if logIvOK b.value then some (b.log (logIv b.value)) else none
    | .contact i =>
        let b := boxes.getD i zeroE
        if contactOK b.value h then
          some (DyadicBivariateJetEnclosure.outerCompose (DyadicContact.enclosure h (contactB h)) b)
        else none
  else none

/-- Run the program; the final register file (newest first), or `none`. -/
def exec (h : DI) : List Shape → List Enc → Option (List Enc)
  | [], boxes => some boxes
  | s :: rest, boxes =>
      match step h s boxes with
      | some o => exec h rest (o :: boxes)
      | none => none

def ckShapes : List Shape := [.inv 3, .mul 3 0, .neg 2, .add 1 0, .mul 5 0, .add 5 0, .add 0 3, .log 7, .mul 8 0, .neg 0, .add 12 7, .log 0, .mul 1 0, .neg 0, .add 4 0, .log 9, .mul 10 0, .neg 0, .neg 12, .add 21 0, .log 0, .mul 1 0, .neg 0, .add 5 0, .add 9 0, .mul 28 18, .inv 0, .mul 2 0, .contact 0, .log 32, .add 32 1, .log 0, .mul 1 0, .neg 4, .add 36 0, .log 0, .mul 1 0, .add 4 0, .mul 0 37, .neg 0, .add 10 0, .mul 12 12, .neg 0, .add 45 0, .log 0, .mul 0 44, .neg 0, .add 17 0, .mul 51 51, .inv 0, .mul 6 0, .mul 54 3, .inv 17, .mul 22 0, .log 0, .mul 14 26, .mul 5 4, .inv 0, .mul 2 0, .add 4 0, .mul 19 19, .mul 20 0, .mul 65 0, .add 11 20, .mul 1 0, .mul 14 14, .mul 41 0, .mul 15 15, .mul 16 0, .mul 2 0, .inv 0, .mul 6 0, .mul 75 0, .inv 73, .mul 63 0, .log 0, .inv 70, .mul 57 0, .log 0, .mul 79 68, .mul 74 60, .add 5 2, .mul 85 22, .add 1 0, .mul 4 0, .mul 88 85, .neg 0, .add 89 0, .mul 12 0, .neg 91, .add 1 0, .mul 84 0, .add 7 0, .inv 17, .mul 1 0, .neg 12, .add 14 0, .mul 16 0, .mul 101 92, .neg 0, .add 102 0, .mul 22 0, .neg 0, .add 105 0, .mul 97 0, .add 7 0, .neg 26, .mul 100 27, .mul 0 32, .inv 84, .mul 1 0, .neg 0, .add 5 0, .mul 106 34, .mul 0 4, .neg 0, .add 118 0, .mul 36 0, .mul 5 5, .mul 46 0, .neg 0, .add 26 0, .mul 49 43, .mul 5 5, .mul 1 0, .neg 0, .add 20 0, .add 47 46, .mul 55 15, .mul 0 11, .add 2 0, .mul 9 4, .mul 1 1, .mul 54 0, .neg 0, .add 3 0]

/-- Initial registers `[a, z, 1, 2]` for value intervals of `a` and `z`. -/
def initial (a z : DI) : List Enc :=
  [DyadicBivariateJetEnclosure.coordinateA a, DyadicBivariateJetEnclosure.coordinateZ z,
   DyadicBivariateJetEnclosure.const 40 1, DyadicBivariateJetEnclosure.const 40 2]

/-! ## Cells -/

/-- Common denominator of box coordinates: `D = 50·2^24` (so `1/50, 1/10, 3/40, 1/5, 1` are exact). -/
def D : ℤ := 838860800

/-- `max |lo| |hi|` of an interval. -/
def mag (i : DI) : ℤ := max |i.lo| |i.hi|

/-- `8 D² S · taylorLower` for box half-widths `A/(2D)`, `Z/(2D)`, as an integer. -/
def taylorZ (c w : Enc) (A Z : ℤ) : ℤ :=
  8 * D ^ 2 * c.value.lo - 4 * D * (mag c.firstA * A + mag c.firstZ * Z) -
    (mag w.secondAA * A ^ 2 + 2 * mag w.secondAZ * A * Z + mag w.secondZZ * Z ^ 2)

/-- Scale-40 outer enclosure of `[n0/d, n1/d]`. -/
def ivZ (n0 n1 d : ℤ) : DI := ⟨floorDiv (n0 * S) d, ceilDiv (n1 * S) d⟩

/-- Contact brackets of one cell: center run and whole-box run. -/
structure Hint where
  hc : DI
  hw : DI
  deriving Repr, DecidableEq

/-- Registers for the box center `((U0+U1)/2D, (R0+R1)/2D)`. -/
def centerRegs (U0 U1 R0 R1 : ℤ) : List Enc :=
  initial (ivZ (U0 + U1) (U0 + U1) (2 * D)) (ivZ (R0 + R1) (R0 + R1) (2 * D))
/-- Registers for the whole box `[U0/D, U1/D] × [R0/D, R1/D]`. -/
def wholeRegs (U0 U1 R0 R1 : ℤ) : List Enc := initial (ivZ U0 U1 D) (ivZ R0 R1 D)

/-- Positivity of the two Taylor bounds from the final register files. -/
def taylorOK (ce wh : List Enc) (A Z : ℤ) : Bool :=
  decide (0 < taylorZ (ce.getD 14 zeroE) (wh.getD 14 zeroE) A Z) &&
  decide (0 < taylorZ (ce.getD 0 zeroE) (wh.getD 0 zeroE) A Z)

/-- The whole per-cell test on `u ∈ [U0/D, U1/D]`, `ρ ∈ [R0/D, R1/D]`. -/
def cellOK (U0 U1 R0 R1 : ℤ) (h : Hint) : Bool :=
  decide (0 < U0) && decide (U0 ≤ U1) && decide (2 * U1 < D) && decide (0 < R0) && decide (R0 ≤ R1) &&
  match exec h.hc ckShapes (centerRegs U0 U1 R0 R1), exec h.hw ckShapes (wholeRegs U0 U1 R0 R1) with
  | some ce, some wh => taylorOK ce wh (U1 - U0) (R1 - R0)
  | _, _ => false

/-- Guillotine cover of a box by accepted cells (split points are integers over `D`). -/
inductive Tree where
  | leaf (h : Hint)
  | su (m : ℤ) (l r : Tree)
  | sr (m : ℤ) (l r : Tree)
  deriving Repr

def treeOK (U0 U1 R0 R1 : ℤ) : Tree → Bool
  | .leaf h => cellOK U0 U1 R0 R1 h
  | .su m l r => decide (U0 ≤ m) && decide (m ≤ U1) && treeOK U0 m R0 R1 l && treeOK m U1 R0 R1 r
  | .sr m l r => decide (R0 ≤ m) && decide (m ≤ R1) && treeOK U0 U1 R0 m l && treeOK U0 U1 m R1 r

end GeneralCK.CKFast


