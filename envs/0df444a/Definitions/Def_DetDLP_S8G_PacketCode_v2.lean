-- Prove2me | Definitions.Def_DetDLP_S8G_PacketCode_v2
-- name    : DetDLP_S8G_PacketCode_v2
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T21:09:55.844117+00:00
-- url     : https://prove2.me/theorems/e88efd0e-936a-4e9e-8bc4-22bf2a30de1c

import Definitions.Def_DetDLP_S8H_MakeCombinators
import Definitions.Def_DetDLP_S8G_Routes
import Definitions.Def_DetDLP_S8G_FpMomentLayout
import Definitions.Def_DetDLP_S8H0_PointGraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork DetDLP_W1_Queries FpAtomRows ResidueWires

def allN (n : ℕ) (f : ℕ → NC) := if n=0 then rowN 0 0 (fun _ _ => 0) else manyN (n-1) f
def bus (n pin o i : ℕ) := if i<n then o+i else pin
def checkN (d pin x y c : ℕ) := colN (d+1) (bus d pin x) (bus d pin y) (fun _ => pin) (c+·)
def seedN (m d pin L : ℕ) :=
  let t := (triple d).size; let s := (seedSlot d).size
  catN (allN m fun i => let o := i*s; catN (checkN d pin o (o+d) (o+2*d)) (catN (checkN d pin (o+t) (o+t+d) (o+t+2*d)) (colN (d+1) (bus d pin o) (fun _ => pin) (bus d pin (o+2*t)) (o+2*t+d+·))))
    (rowN L 1 fun i _ => let b := d-1; let o := i/b/2*s; if i < m*2*b then (if i/b%2=0 then o+2*t else o+t)+(b-1-i%b) else pin)
def atomN (d e pin o a b : ℕ) :=
  let t := (triple d).size; let r := o+t+d+(d+(d+1)); let rem := r+t; let q := rem+t; let l := q+d; let k := l+2*d+e; let cp := k+2*d+e; let h := cp+1
  catN (checkN d pin o (o+d) (o+2*d)) (catN (scanN d (bus d pin o) (o+t+·) pin) (catN (checkN d pin r (r+d) (r+2*d)) (catN (checkN d pin r (o+t+d) (o+t+2*d)) (catN (checkN d pin rem (rem+d) (rem+2*d))
    (genHashN d e (l+2*d) (k+2*d) pin (bus d pin a) (bus d pin o) (bus d pin b) (bus d pin r) (bus d pin rem) (bus d pin q) (bus (2*d) pin l) (bus (2*d) pin k) (bus (d+1) pin (h+2*d)) (fun _ => cp) (h+·) (h+2*d+(d+1)+·) (h+2*d+(d+1)+(d+1)+·))))))
def chainN (m d e pin res base atomBase : ℕ) :=
  let n := m-1; let w := (stageShape d e).size; let t := (triple d).size; let tmp := base+n*w; let aw := (atomSlot d e).size
  catN (rowN (if n=0 then d else 0) 2 fun i k => if k=0 then bus d pin atomBase i else bus d pin res i) (catN (allN (n-1) fun i => let o := tmp+i*t; checkN d pin o (o+d) (o+2*d)) (allN n fun i =>
    let o := base+i*w; let l := o+d; let k := l+2*d+e; let x := if i=0 then atomBase else tmp+(i-1)*t; let z := if i<n-1 then tmp+i*t else res
    catN (catN (prodN d e (l+2*d) (bus d pin x) (bus d pin (atomBase+(i+1)*aw)) (bus (2*d) pin l)) (prodN d e (k+2*d) (bus d pin o) (fun _ => pin) (bus (2*d) pin k))) (colN (2*d) (bus (2*d) pin k) (bus d pin z) (bus (2*d) pin l) (k+2*d+e+·))))
def tree (m d e c v L : ℕ) :=
  let t := (triple d).size; let s := (seedSlot d).size; let a := (atomSlot d e).size; let w := (chainShape (m-1) d e).size
  let o := m*s; let r := o+c*(m*a); let pin := o+(c*(m*a)+v*(t+c*w))
  catN (anchorN (pin+1) id) (catN (anchorN 1 (fun _ => pin)) (catN (seedN m d pin L) (catN (allN c fun k => allN m fun i => atomN d e pin (o+k*(m*a)+i*a) (i*s+2*t) (i*s+t))
    (allN v fun j => let z := r+j*(t+c*w); catN (checkN d pin z (z+d) (z+2*d)) (allN c fun k => chainN m d e pin z (z+t+k*w) (o+k*(m*a)))))))
def networkCode (w : PacketWord) := let b := width (prime w); let d := b+1; let i := idx w; tree (slots b) d (PointAddresses.wires d) (min i 2) (if i=3 then 1 else 0) (pfx w).length
def make := fullMake networkCode sizeField
def anchored {k} (b : B k) : B k := ⟨AnchoredLayout.block b.core k,AnchoredLayout.signal b.core b.name⟩
theorem anchors_fit {k} {b : B k} {c} (hc : Fits c b) : Fits (catN (anchorN k id) c) (anchored b) := by
  refine ⟨PointAddresses.sum_spec ⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩ hc.1,fun i => ?_⟩; induction i using Fin.addCases with
  | left i => change (if i.val < k then i.val else c.2 (i.val-k)) = (Fin.addCases (motive:=fun _ => Fin k) id b.name ((⟨i.val,i.isLt⟩ : Fin k).castAdd _)).val; rw [Fin.addCases_left,if_pos (show i.val < k from i.isLt)]; rfl
  | right i => change (if k+i.val < k then _ else c.2 (k+i.val-k)) = (Fin.addCases (motive:=fun _ => Fin k) id b.name (Fin.natAdd k i)).val; rw [Fin.addCases_right]; simpa using hc.2 i

end DetDLP.S8G.MakePacketV2


