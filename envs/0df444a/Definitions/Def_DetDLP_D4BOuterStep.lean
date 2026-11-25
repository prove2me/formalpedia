-- Prove2me | Definitions.Def_DetDLP_D4BOuterStep
-- name    : DetDLP_D4BOuterStep
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:03:41.5279+00:00
-- url     : https://prove2.me/theorems/1e618d5a-fe06-4b7e-8e61-2a713fb212d6
-- title:
--   Outer scalar-cursor oracle step
-- statement:
--   A uniform bit-word controller for small instances, rank enumeration, and scalar contractions. Binary bounds are expanded over repeated header calls. A reflected carry test finds the first incrementable coordinate of the little-endian digit vector; the three arithmetic kernels implement the branch and final accumulations.

import Definitions.Def_DetDLP_D4BEntryCall
import Definitions.Def_DetDLP_F9A1_BAddRead
import Definitions.Def_DetDLP_F9A2_BMul
import Definitions.Def_DetDLP_F9A3_BUnpackTerm
set_option autoImplicit false
namespace DetDLP.D4BOuter
open Groundwork Groundwork.PolyT D4BEntry D4Slice DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev Bits := List Bool

def dispatch (st : Bits) (tag : ℕ) (query : Bits) := false :: pair st
  (if tag = 0 then false :: query else true :: decide (tag = 2) :: query)
def rank (x : Bits) (i : ℕ) := listWord [x,countWord i]
def headerCall (x buf : Bits) := dispatch (listWord [countWord 1,x,buf]) 1 (rank x 0)
/-- Context fields: original input, header, modulus, guard divisor, unary row
count, unary degree, encoded lower coefficients, canonical zero residue. -/
def context (x hd buf : Bits) :=
  let d := field 2 hd; let g := nval 1 hd; let q := g + nval 6 x
  let rows := clipped (nval 7 x) buf
  listWord [x, hd, modBits q buf, modBits g buf, rows, d.map (fun _ => true),
    encodeNatListBin (d.map fun b => if b then 1 else 0),
    encodeNatListBin (rows.flatMap fun _ => d.map fun _ => 0)]
def readOut (ctx acc : Bits) := true :: F9A1.bReadZeroDivRaw
  (listWord [field 3 ctx, field 5 ctx, field 4 ctx, acc])
def branchCall (ctx acc : Bits) (u : ℕ) := dispatch
  (listWord [countWord 2,ctx,acc,countWord u]) 1 (rank (field 0 ctx) (u+1))
def afterHeader (x hd buf : Bits) :=
  if buf.length < max (nval 1 hd + nval 6 x) (nval 7 x) then headerCall x (true :: (buf ++ buf)) else
  let ctx := context x hd buf; let acc := field 7 ctx
  if nval 0 hd = 0 then readOut ctx acc else branchCall ctx acc 0
/-- The side-bit word supplies an explicit unary witness of the vertex count. -/
def sides (br : Bits) := field 2 (field 0 br)
def width (br : Bits) := max 1 (nval 1 (field 0 br) / ((sides br).length + 1))
def radix (ctx br : Bits) := (nval 1 (field 1 ctx) + nval 6 (field 0 ctx)) / width br + 1
def spaces (ctx br : Bits) := true :: (sides br).flatMap (fun _ => (field 5 ctx).tail)
def digitCall (ctx acc : Bits) (u : ℕ) (br av ba : Bits) :=
  let x := field 0 ctx; let d := (field 5 ctx).length; let l := (field 4 ctx).length
  let n := (sides br).length; let g := field 0 br; let e := nval 1 g
  let pp := e + n * width br + n * Nat.clog 2 (d*l) + 2
  let desc := listWord [x,field 1 ctx,br,av]
  dispatch (listWord [countWord 3,ctx,acc,countWord u,br,av,ba]) 2
    (listWord [desc,g,field 2 x,countWord pp,countWord ((spaces ctx br).length*l)])
def afterBranch (ctx acc : Bits) (u : ℕ) (br : Bits) := digitCall ctx acc u br
  (encodeNatListBin ((sides br).map fun _ => 0)) (field 7 ctx)
def term (ctx br : Bits) (a : List ℕ) (ans : Bits) :=
  let r := width br * a.sum; let q := nval 1 (field 1 ctx) + nval 6 (field 0 ctx)
  let scalar := if r < q then modBits r (field 2 ctx) else (0 : ℕ).bits
  ResidualScalarOracle.bUnpackTermRaw (listWord [field 2 ctx,scalar,field 4 ctx,
    spaces ctx br,field 6 ctx,ans])
def add (ctx x y : Bits) := F9A1.bAddRaw (listWord [field 2 ctx,x,y])
def mul (ctx x y : Bits) := F9A2.bMulRaw (listWord [field 2 ctx,field 4 ctx,field 5 ctx,field 6 ctx,x,y])
def nextAt (a : List ℕ) (j : ℕ) := (a.map (fun v => decide (v+1 < j))).idxOf true
def advanceVec (a : List ℕ) (i : ℕ) := encodeNatListBin ((List.range a.length).map fun k =>
  if k < i then 0 else if k = i then a.getD k 0 + 1 else a.getD k 0)
def afterDigit (st ans : Bits) :=
  let ctx := field 1 st; let acc := field 2 st; let u := nval 3 st
  let br := field 4 st; let a := w5_M6Sort.decode (field 5 st)
  let ba := add ctx (field 6 st) (term ctx br a ans); let i := nextAt a (radix ctx br)
  if i < a.length then digitCall ctx acc u br (advanceVec a i) ba else
  let acc' := add ctx acc (mul ctx (field 1 br) ba)
  if u+1 < nval 0 (field 1 ctx) then branchCall ctx acc' (u+1) else readOut ctx acc'
def step (L₀ : ℕ) (w : Bits) :=
  let st := first (true :: w); let ans := more (true :: w)
  if ans = [] then
    if Nat.clog 2 (nval 5 st) < L₀ then dispatch (listWord [countWord 0]) 0 st
    else headerCall st []
  else if nval 0 st = 0 then true :: ans
  else if nval 0 st = 1 then afterHeader (field 1 st) ans (field 2 st)
  else if nval 0 st = 2 then afterBranch (field 1 st) (field 2 st) (nval 3 st) ans
  else afterDigit st ans
end DetDLP.D4BOuter
abbrev DetDLP.outerStep := DetDLP.D4BOuter.step


