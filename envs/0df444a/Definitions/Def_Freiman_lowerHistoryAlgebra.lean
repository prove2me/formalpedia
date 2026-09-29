-- Prove2me | Definitions.Def_Freiman_lowerHistoryAlgebra
-- name    : Freiman_lowerHistoryAlgebra
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:50:14.080029+00:00
-- url     : https://prove2.me/theorems/2f176456-e870-43c4-8cc7-a2b6d51e8a57
-- title:
--   Freiman.lowerHistoryAlgebra
-- statement:
--   Exact Q(sqrt3,sqrt7) arithmetic, continuant matrices, threshold pullback, endpoint case expressions and signed comparisons. Source: Freiman's Hall ray: Proof report and corrected English text (8 September 2026); history_certificates.tex app:all-suffix-histories, global_selection.tex lem:global-suffix-targets; initial_bridges.tex lem:H-entry-bridges; certificates/target_selection/all_suffix_histories_printed.json.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Appendix app:all-suffix-histories and its exact arithmetic/certificate guide.

import Definitions.Def_Freiman_lowerCertificates
import Definitions.Def_Freiman_certificates

namespace Freiman

def lowerHistoryRat (q : ℚ) : CertField := ⟨q,0,0,0⟩
def lowerHistoryNeg (z : CertField) : CertField := certFieldScale (-1) z
def lowerHistoryInv (z : CertField) : CertField :=
  let u := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2
  let v := 2*z.a*z.b - 14*z.c*z.d
  certFieldScale (1/(u^2-3*v^2))
    (certFieldMul ⟨z.a,z.b,-z.c,-z.d⟩ ⟨u,-v,0,0⟩)
def lowerHistoryDiv (x y : CertField) : CertField := certFieldMul x (lowerHistoryInv y)
def lowerHistoryRatSign (q : ℚ) : ℤ := if 0 < q then 1 else if q < 0 then -1 else 0
def lowerHistoryQuadSign (a b : ℚ) (d : ℕ) : ℤ :=
  if a = 0 then lowerHistoryRatSign b else
  if b = 0 then lowerHistoryRatSign a else
  if 0 < a then
    if 0 < b then 1 else lowerHistoryRatSign (a^2-d*b^2)
  else if b < 0 then -1 else -lowerHistoryRatSign (a^2-d*b^2)
def lowerHistorySign (z : CertField) : ℤ :=
  let x := lowerHistoryQuadSign z.a z.b 3
  let y := lowerHistoryQuadSign z.c z.d 3
  let u := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2
  let v := 2*z.a*z.b - 14*z.c*z.d
  if x = 0 then y else if y = 0 then x else
  if 0 < x then (if 0 < y then 1 else lowerHistoryQuadSign u v 3)
  else if y < 0 then -1 else -lowerHistoryQuadSign u v 3
def lowerHistoryAbs (z : CertField) : CertField :=
  if lowerHistorySign z < 0 then lowerHistoryNeg z else z
def lowerHistoryLex (x y : CertField) : Bool := decide
  (x.a < y.a ∨ (x.a = y.a ∧ (x.b < y.b ∨ (x.b = y.b ∧
    (x.c < y.c ∨ (x.c = y.c ∧ x.d ≤ y.d))))))
def lowerHistorySort (x y : CertField) : CertField × CertField :=
  if lowerHistoryLex x y then (x,y) else (y,x)
def lowerHistoryThreshold (c : CertField) (x y : CertField × CertField) : CertThreshold :=
  let xx := lowerHistorySort x.1 x.2
  let yy := lowerHistorySort y.1 y.2
  ⟨c,xx.1,xx.2,yy.1,yy.2⟩
def lowerHistoryMatrix (w : List ℕ+) : (ℕ × ℕ) × (ℕ × ℕ) :=
  w.foldl (fun m a => ((m.1.2,m.1.1+(a:ℕ)*m.1.2),
    (m.2.2,m.2.1+(a:ℕ)*m.2.2))) ((1,0),(0,1))
def lowerHistoryCF (w : List ℕ+) (z : CertField) : CertField :=
  let m := lowerHistoryMatrix w
  lowerHistoryDiv (certFieldAdd (certFieldScale m.1.1 z) (lowerHistoryRat m.1.2))
    (certFieldAdd (certFieldScale m.2.1 z) (lowerHistoryRat m.2.2))
def lowerHistoryAlpha : CertField := ⟨-1/2,0,0,1/6⟩
def lowerHistoryBeta : CertField := ⟨-3/2,0,0,1/2⟩
def lowerHistoryTau : CertField := ⟨-1,1,0,0⟩
def lowerHistoryWH (w : LowerPair) : CertThreshold :=
  let x := (lowerHistoryCF w.1 lowerHistoryAlpha,lowerHistoryCF w.1 lowerHistoryBeta)
  let y := (lowerHistoryCF w.2 lowerHistoryAlpha,lowerHistoryCF w.2 lowerHistoryBeta)
  lowerHistoryThreshold (lowerHistoryAbs (lowerHistoryDiv
    (certFieldSub x.1 x.2) (certFieldSub y.1 y.2))) x y
def lowerHistoryScaleThreshold (q : ℚ) (h : CertThreshold) : CertThreshold :=
  { h with c := certFieldScale q h.c }
def lowerHistoryComplement (b : CertBound) : CertBound :=
  { b with lower := !b.lower, strict := !b.strict }
def lowerHistoryPull (b : CertBound) (words : LowerPair) (orientation : Bool) : CertBound :=
  let t := b.threshold
  let h := if orientation then
    lowerHistoryThreshold (lowerHistoryInv t.c) (t.y0,t.y1) (t.x0,t.x1) else t
  let m := lowerHistoryMatrix words.1
  let n := lowerHistoryMatrix words.2
  let fac (c d : ℕ) (z : CertField) := certFieldAdd (lowerHistoryRat d) (certFieldScale c z)
  let c := lowerHistoryDiv
    (certFieldMul h.c (certFieldMul (fac n.2.1 n.2.2 h.y0) (fac n.2.1 n.2.2 h.y1)))
    (certFieldMul (fac m.2.1 m.2.2 h.x0) (fac m.2.1 m.2.2 h.x1))
  ⟨if orientation then !b.lower else b.lower,b.strict,
    lowerHistoryThreshold c (lowerHistoryCF words.1 h.x0,lowerHistoryCF words.1 h.x1)
      (lowerHistoryCF words.2 h.y0,lowerHistoryCF words.2 h.y1)⟩

-- A context records suffixes and relative parity; common odd base parity is
-- removed by the report's increasing local coordinate.
structure LowerHistoryContext where
  words : LowerPair
  parity : Bool × Bool
  deriving DecidableEq

def lowerHistoryPick {α : Type} (p : α × α) (side : Bool) : α := if side then p.2 else p.1
def lowerHistorySet {α : Type} (p : α × α) (side : Bool) (x : α) : α × α :=
  if side then (p.1,x) else (x,p.2)
def lowerHistoryWordParity (C : LowerHistoryContext) (w : LowerPair) (side : Bool) : Bool :=
  xor (lowerHistoryPick C.parity side) (decide ((lowerHistoryPick w side).length % 2 = 1))
def lowerHistoryNatural (C : LowerHistoryContext) (w : LowerPair) (upper side : Bool) : Bool :=
  let tail3 := xor (!upper) (lowerHistoryWordParity C w side)
  decide ((if tail3 then [3,1] else [3] : List ℕ+).IsSuffix
    (lowerHistoryPick C.words side ++ lowerHistoryPick w side))
def lowerHistoryEndVal (C : LowerHistoryContext) (w : LowerPair) (upper side short : Bool) : CertField :=
  let tail3 := xor (!upper) (lowerHistoryWordParity C w side)
  let ext : List ℕ+ := if tail3 then (if short then [2,1,3] else [3])
    else (if short then [1,2,1,3] else [1,3])
  lowerHistoryCF (lowerHistoryPick w side ++ ext) lowerHistoryTau
abbrev LowerHistoryEndCase := (CertField × CertField) × List CertBound
def lowerHistoryNormalCases (w : LowerPair) : List (Bool × CertBound) :=
  [(false,⟨false,false,lowerHistoryWH w⟩),(true,⟨true,false,lowerHistoryWH w⟩)]
def lowerHistoryEqualCases (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : List LowerHistoryEndCase :=
  let n := (lowerHistoryNatural C w upper false,lowerHistoryNatural C w upper true)
  if n.1 || n.2 then
    [((lowerHistoryEndVal C w upper false n.1,lowerHistoryEndVal C w upper true n.2),[])]
  else
    let e : List ℕ+ := if xor (!upper) (lowerHistoryWordParity C w false) then [3] else [1,3]
    let aux := lowerHistoryWH (w.1++e,w.2++e)
    (lowerHistoryNormalCases w).flatMap fun (wide,norm) =>
      let cut : CertBound := if wide then ⟨false,false,lowerHistoryScaleThreshold (7/5) aux⟩
        else ⟨true,false,lowerHistoryScaleThreshold (5/7) aux⟩
      [false,true].map fun shortened =>
        ((lowerHistoryEndVal C w upper false (shortened && wide),
          lowerHistoryEndVal C w upper true (shortened && !wide)),
          [norm,if shortened then cut else lowerHistoryComplement cut])
def lowerHistoryEndpointCases (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : List LowerHistoryEndCase :=
  if lowerHistoryWordParity C w false = lowerHistoryWordParity C w true then
    lowerHistoryEqualCases C w upper
  else (lowerHistoryNormalCases w).flatMap fun (wide,norm) =>
    let vs := if upper = !(lowerHistoryWordParity C w wide) then
      lowerHistoryEqualCases C (lowerHistorySet w wide (lowerHistoryPick w wide ++ [1])) upper
    else [((lowerHistoryEndVal C w upper false (lowerHistoryNatural C w upper false),
            lowerHistoryEndVal C w upper true (lowerHistoryNatural C w upper true)),[])]
    vs.map fun (v,cs) => (v,norm::cs)
inductive LowerHistoryComparison where
  | automatic | impossible | bound (b : CertBound)
  deriving DecidableEq
def lowerHistoryGreater (C : LowerHistoryContext) (x y : CertField × CertField) : LowerHistoryComparison :=
  let dx := certFieldSub x.1 y.1
  let dy := certFieldSub x.2 y.2
  let sx := (if C.parity.1 then -1 else 1) * lowerHistorySign dx
  let sy := (if C.parity.2 then -1 else 1) * lowerHistorySign dy
  if 0 ≤ sx ∧ 0 ≤ sy then .automatic else
  if sx ≤ 0 ∧ sy ≤ 0 then .impossible else
  .bound ⟨decide (sx < 0),false,lowerHistoryThreshold
    (lowerHistoryAbs (lowerHistoryDiv dx dy)) (x.1,y.1) (x.2,y.2)⟩
def lowerHistoryComparisons (C : LowerHistoryContext) (u v : LowerPair) (a b : Bool) :
    List (List CertBound × LowerHistoryComparison) :=
  (lowerHistoryEndpointCases C u a).flatMap fun (x,cx) =>
    (lowerHistoryEndpointCases C v b).map fun (y,cy) =>
      (cx++cy,lowerHistoryGreater C x y)

end Freiman


