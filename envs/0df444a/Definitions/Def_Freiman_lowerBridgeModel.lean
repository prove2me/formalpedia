-- Prove2me | Definitions.Def_Freiman_lowerBridgeModel
-- name    : Freiman_lowerBridgeModel
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:20:52.552003+00:00
-- url     : https://prove2.me/theorems/578dfa8c-af6a-4793-bb26-f3dfb74c0b14
-- title:
--   Freiman marked initial bridges: lowerBridgeModel
-- statement:
--   Exact source matrices, finite polynomial and endpoint data for the six marked initial bridge cases.
-- source:
--   Freiman report, initial_bridges.tex; certificates/target_selection/H_entry_bridges.json

import Definitions.Def_Freiman_lowerInitialEntry
namespace Freiman
inductive LowerBridgeCase where
  | aZero | aPos | bZero | bPos | cZero | cPos
  deriving DecidableEq

def lowerBridgeSeamCase : LowerBridgeCase → LowerInitialSeamCase
  | .aZero => .aZero | .aPos => .aPos
  | .bZero => .b18Zero | .bPos => .b18Pos
  | .cZero => .cZero | .cPos => .cPos

def lowerBridgeFamily (c : LowerBridgeCase) : LowerInitialFamily :=
  lowerInitialSeamFamily (lowerBridgeSeamCase c)
def lowerBridgeZero (c : LowerBridgeCase) : Bool :=
  lowerInitialSeamZero (lowerBridgeSeamCase c)
def lowerBridgeK (c : LowerBridgeCase) (k : ℕ) : ℕ := if lowerBridgeFamily c = .C then k else 0
noncomputable def lowerBridgePair (c : LowerBridgeCase) (n k : ℕ) : LowerPair :=
  lowerNormalize (lowerFamilyPair (lowerBridgeFamily c) n (lowerBridgeK c k) 0)
noncomputable def lowerBridgeMatrices (c : LowerBridgeCase) (x y : ℝ) : LowerInitialMatrix × LowerInitialMatrix :=
  lowerInitialSeamMatrices (lowerBridgeSeamCase c) x (if lowerBridgeFamily c=.C then y else 0) 0
noncomputable def lowerBridgeCommonMatrices (c : LowerBridgeCase) (x y : ℝ) : LowerInitialMatrix × LowerInitialMatrix :=
  let mul := lowerInitialMatMul
  let M := lowerInitialWordMatrix
  let P := lowerInitialP (lowerBridgeZero c) x
  (mul (mul (mul (M [3,2,1,1]) P) (M [3,1,3,1,2])) (lowerInitialK y),
   mul (mul (mul (M [4,3,2,2]) P) (M [3,1])) (lowerInitialK y))
noncomputable def lowerBridgeCommonPair (c : LowerBridgeCase) (n k : ℕ) : LowerPair :=
  if lowerBridgeFamily c = .C then
    ([3,2,1,1]++lowerRepeat lowerPeriod n++[3,1,3,1,2]++List.replicate (k+1) 3,
     [4,3,2,2]++lowerRepeat lowerPeriod n++[3,1]++List.replicate (k+1) 3)
  else lowerBridgePair c n k
noncomputable def lowerBridgeMatAppend (m : LowerInitialMatrix × LowerInitialMatrix) (w : LowerPair) :=
  (lowerInitialMatMul m.1 (lowerInitialWordMatrix w.1),
   lowerInitialMatMul m.2 (lowerInitialWordMatrix w.2))
noncomputable def lowerBridgeWidthDen (m : LowerInitialMatrix) : ℝ :=
  lowerInitialMatDen m lowerAlpha * lowerInitialMatDen m lowerBeta
noncomputable def lowerBridgeDifference (m : LowerInitialMatrix × LowerInitialMatrix)
    (u v : LowerPair) (opposite : Bool) : ℝ :=
  let a := prefixEval u.1 lowerTau
  let b := prefixEval v.1 lowerTau
  let c := prefixEval u.2 lowerTau
  let d := prefixEval v.2 lowerTau
  (a-b)*lowerInitialMatDen m.2 c*lowerInitialMatDen m.2 d +
    (if opposite then -(c-d) else c-d)*lowerInitialMatDen m.1 a*lowerInitialMatDen m.1 b
inductive LowerBridgeRecordKind where
  | width | auxiliary | h7 | notA9 | fork | chain | lowerStrip | upperStrip | cLower | cUpper
  deriving DecidableEq
structure LowerBridgeRecord where
  kind : LowerBridgeRecordKind
  words : LowerPair
  wider : Bool
  high : Bool
  short : Bool
  suffix : List ℕ+
  upperWords : LowerPair
  lowerWords : LowerPair
  strict : Bool
  polynomial : CertPoly22
noncomputable def lowerBridgeNumerator (c : LowerBridgeCase) (r : LowerBridgeRecord) (x y : ℝ) : ℝ :=
  let m := lowerBridgeMatrices c x y
  let w := lowerBridgeMatAppend m r.words
  let wide := if r.wider then w.2 else w.1
  let other := if r.wider then w.1 else w.2
  match r.kind with
  | .width => lowerBridgeWidthDen other - lowerBridgeWidthDen wide
  | .auxiliary =>
    let a := lowerInitialMatMul wide (lowerInitialWordMatrix r.suffix)
    let b := lowerInitialMatMul other (lowerInitialWordMatrix r.suffix)
    (if r.short then 1 else -1)*(7*lowerBridgeWidthDen a-5*lowerBridgeWidthDen b)
  | .h7 => lowerInitialMatDen w.1 (lowerTheta 3)*lowerInitialMatDen w.1 (lowerTheta 25)-
      (31/100:ℝ)*lowerInitialMatDen w.2 (lowerTheta 63)*lowerInitialMatDen w.2 (lowerTheta 66)
  | .notA9 => lowerInitialMatDen w.1 (lowerTheta 36)*lowerInitialMatDen w.1 (lowerTheta 63)-
      ((3-Real.sqrt 3)/2)*lowerInitialMatDen w.2 (lowerTheta 63)*lowerInitialMatDen w.2 (lowerTheta 66)
  | .cLower | .cUpper => lowerBridgeDifference (lowerBridgeCommonMatrices c x y) r.upperWords r.lowerWords true
  | _ => lowerBridgeDifference m r.upperWords r.lowerWords false

def lowerBridgeRectangle : CertRectangle := ⟨0,1/85,0,1/3⟩
def lowerBridgeChecked (r : LowerBridgeRecord) : Prop :=
  ∀ i j : Fin 3, 0 < certFieldLower (certBernsteinCoefficients r.polynomial lowerBridgeRectangle i j)
noncomputable def lowerBridgeAppend (p w : LowerPair) : LowerPair := (p.1++w.1,p.2++w.2)
noncomputable def lowerBridgeRecordFact (c : LowerBridgeCase) (n k : ℕ) (r : LowerBridgeRecord) : Prop :=
  let p := lowerBridgePair c n k
  let w := lowerBridgeAppend p r.words
  let wide := if r.wider then w.2 else w.1
  let other := if r.wider then w.1 else w.2
  match r.kind with
  | .width => lowerWidth other < lowerWidth wide
  | .auxiliary => if r.short then lowerWidth (wide++r.suffix) ≤ (7/5:ℝ)*lowerWidth (other++r.suffix)
      else (7/5:ℝ)*lowerWidth (other++r.suffix) < lowerWidth (wide++r.suffix)
  | .h7 => lowerThreshold w (31/100) 3 63 25 66 ≤ lowerScale (lowerNormalize w)
  | .notA9 => ¬ lowerA w 9
  | .cLower | .cUpper =>
    let b := lowerBridgeCommonPair c n k
    0 < (-1:ℝ)^b.1.length *
      (prefixEval (b.1++r.upperWords.1) lowerTau + prefixEval (b.2++r.upperWords.2) lowerTau -
       prefixEval (b.1++r.lowerWords.1) lowerTau - prefixEval (b.2++r.lowerWords.2) lowerTau)
  | _ => 0 < (-1:ℝ)^p.1.length *
      (prefixEval (p.1++r.upperWords.1) lowerTau + prefixEval (p.2++r.upperWords.2) lowerTau -
       prefixEval (p.1++r.lowerWords.1) lowerTau - prefixEval (p.2++r.lowerWords.2) lowerTau)
structure LowerBridgeEndpoint where
  words : LowerPair
  high : Bool
  tails : LowerPair
noncomputable def lowerBridgeEndpointFact (c : LowerBridgeCase) (n k : ℕ) (e : LowerBridgeEndpoint) : Prop :=
  let p := lowerBridgePair c n k
  lowerEndpoint (lowerBridgeAppend p e.words)
    (if p.1.length % 2 = 0 then e.high else !e.high) =
      4+prefixEval (p.1++e.tails.1) lowerTau+prefixEval (p.2++e.tails.2) lowerTau
end Freiman


