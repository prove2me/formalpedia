-- Prove2me | Definitions.Def_DetDLP_M3A_FpPolyDefs
-- name    : DetDLP_M3A_FpPolyDefs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T21:10:34.257194+00:00
-- url     : https://prove2.me/theorems/6aaf4b0f-e0ee-4e8b-bebd-1ca42b325ea0
-- title:
--   Total native finite-field packet and port-entry functions
-- statement:
--   Defines the terminal packet builder and local evaluator on all bit strings, including affine lookup with signed falling-factorial coefficients.
-- source:
--   DetDLP Stage II, Section 4, native finite-field lookup separator.

import Definitions.Def_DetDLP_M3A_FpArithNet
import Definitions.Def_DetDLP_S8H_WirePacket
import Definitions.Def_DetDLP_S8J_HashGatePoly
import Definitions.Def_DetDLP_S8A_FpPrefixStep

set_option autoImplicit false
namespace DetDLP.M3A.FpPolyDefs
open Groundwork S8H.PointAddresses S8L.FpPair.Address S8H.WirePacket S8H0.AnchoredLayout
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev W := List Bool
abbrev fld := m89_enum_words.fields
def field (w : W) (i : ℕ) := (fld w).getD i []
def nums (w : W) := w5_M6Sort.decode w
def num (w : W) (i : ℕ) := (nums w).getD i 0
def prime (w : W) := num (field w 0) 0
def target (w : W) := num (field w 0) 1
def groupSize (w : W) := num (field w 0) 2
def threshold (w : W) := num (field w 0) 3
def blocks (w : W) := (fld (field w 2)).map nums
def m (w : W) := (fld (field w 2)).length
def width (x : ℕ) := (x-1).bits.length
def d (w : W) := width (prime w)
def k (w : W) := width (2*threshold w)
def pre (w : W) := field w 4
def prec (w : W) := 2+4*m w*k w+dFilt (2*m w)*width (2*(2*m w)*groupSize w+2)
def len (w : W) := dFilt (2*m w)+1
def sizeField (w : W) := 2*(70000*m w*(d w+3)+16*m w*k w+1)+prec w

def splice (a : Code) (n : ℕ) (l r : ℕ → ℕ) : Code :=
  ⟨a.ng+n,a.nb,a.ne+(n+n),fun e => if e<a.ne then a.gate e else a.ng+(if e-a.ne<n then e-a.ne else e-a.ne-n),
   fun e => if e<a.ne then a.bit e else if e-a.ne<n then l (e-a.ne) else r (e-a.ne-n)⟩
def addrN (d i lane : ℕ) := 2*(mul d).nb+4*i+lane
def linked (d : ℕ) := splice (stageCode d) (4*d)
  (fun e => if e<2*d then addrN d e 0 else addrN d (e-2*d) 2)
  (fun e => if e<2*d then (mul d).nb+w4_M5EdgeNat.edgeBase d 9 e else w4_M5EdgeNat.edgeBase d 9 (e-2*d))
def stage (d : ℕ) := splice (sum (linked d) (add (d+1))) d (fun i => (linked d).nb+4*i) (fun i => addrN d i 1)
def slot (d k : ℕ) := FpSlotTile.slotCode d k
def xPort (d : ℕ) (i : ℕ) := (linked d).nb+4*(d+1+i)+2
def zPort (d : ℕ) := (linked d).nb+8*(d+1)*4
def sPort (m d k s i : ℕ) := 4*m*(slot d k).nb+s*(stage d).nb+i
def base (m d k : ℕ) := let b := repeatCode (2*m) (stage d); sum (repeatCode (4*m) (slot d k)) (sum b b)
def tie (right : Bool) (m d k e : ℕ) :=
  let n := 4*m*d; let u := if e<n then e else e-n; let s := u/d; let j := u%d; let t := s%(2*m); let b := s/(2*m)
  if e<n then if right then sPort m d k s (d+j) else s*(slot d k).nb+xPort d j
  else if t=0 then sPort m d k ((if right then 1-b else b)*(2*m)+(2*m-1)) ((linked d).nb+4*j)
  else if right then sPort m d k s j else sPort m d k (s-1) ((linked d).nb+4*j)
def chains (m d k : ℕ) := splice (base m d k) (2*(4*m*d)) (tie false m d k) (tie true m d k)
def prefixAddr (m d k u : ℕ) := let s := u/d; ((s/(2*m)*(2*m)+(s%2)*m+s/2%m)%(4*m))*(slot d k).nb+xPort d (u%d)
def arith (m d k plen : ℕ) := let a := chains m d k; let n := min plen (4*m*d)
  splice (sum a (anchorCode (n+1))) n (prefixAddr m d k) (fun i => a.nb+i)
def whole (m d k plen : ℕ) := M3B.ECLayout.code (arith m d k plen) (4*m) k (fun s j => s*(slot d k).nb+zPort d+j)
def fpBuild (w : W) : W :=
  let a := whole (m w) (d w) (k w) (pre w).length; let g := (arith (m w) (d w) (k w) (pre w).length).ng
  Encoding.encodeList id [w,packet (a.ng+a.nb) a.ne a.gate (fun e => a.ng+a.bit e),countWord (d w),countWord (m w),countWord (k w),countWord (sizeField w),countWord (prec w),countWord (len w),
    (List.range (a.ng+a.nb+a.ne)).map (fun v => decide (g ≤ v ∧ v<a.ng))]

def bit (a : W) (j : ℕ) := a.getD j false
def equal (a : W) := a.all (fun b => b == bit a 0)
def col (n i : ℕ) (cin : Bool) (a : W) := decide ((bit a 0).toNat+(bit a 1).toNat+(if i=0 then cin else bit a 4).toNat=(bit a 2).toNat+2*(bit a 3).toNat ∧ (i+1=n → bit a 3=false))
def rows (d p T g : ℕ) (a : W) :=
  let j := g/(d+1); let i := g%(d+1); let x := bit a 0; let y := bit a 1; let z := bit a 2; let c := bit a 3
  if j=7 then decide (x=c ∧ z=false ∧ (i≠0 → x=bit a 4) ∧ y=(x && p.testBit i)) else
  col (d+1) i (decide (j<5)) a && decide ((j<2 → y=false ∧ (i=d → z=false)) ∧ (j=0 ∧ i=d → x=false) ∧
    (j=2 ∨ j=4 → z=p.testBit i) ∧ (j=3 → z=(min T p).testBit i) ∧ (j=5 ∧ i=d → x=false ∧ y=false))
/-- Sort the half-edge incidence bits back into the W4 graph's original edge order. -/
def mulCheck (d g : ℕ) (a : W) :=
  let es := w4_M5GateOps.portList (List.replicate d ()) g
  let half := es.filter (fun e => w4_M5EdgeNat.srcNat d e == g) ++ es.filter (fun e => w4_M5EdgeNat.srcNat d e != g)
  S8J.HashGatePoly.mulLayoutCheck d g (es.map fun e => a.getD (half.idxOf e) false)
def linkedGate (d g : ℕ) (a : W) := let M := (mul d).ng
  if g < 2*M then mulCheck d (g%M) a else if g < (stageCode d).ng then col (2*d) (g-2*M) false a else equal a
/-- Gate-local pins are checked at *every* incidence of a pinned register. -/
def pin (d : ℕ) (ports : List (ℕ × Bool)) (ix : ℕ → ℕ) (val : ℕ → Bool) :=
  ports.all fun t => (List.range d).all fun i => decide (t.1=ix i → t.2=val i)
def localPorts (c : Code) (g : ℕ) (a : W) := ((List.range c.ne).filter fun e => c.gate e == g).map c.bit |>.zip a
def stagePins (d p : ℕ) (ps : List (ℕ × Bool)) := pin d ps (fun j => (mul d).nb+(d+j)) (fun i => p.testBit i) && pin d ps (fun j => addrN d (d+j) 1) (fun _ => false)
def slotGate (d k p T slope intercept g : ℕ) (a : W) :=
  let l := linked d; let e := l.ng+8*(d+1); let ph := e+3*d+5*(d+1); let ps := localPorts (slot d k) g a
  let inner := if g<l.ng then linkedGate d g a && stagePins d p ps else if g<e then rows d p T (g-l.ng) a else equal a
  if g<ph then inner && pin d ps (fun j => l.nb+4*j) (fun j => slope.testBit j) && pin d ps (fun j => l.nb+4*(5*(d+1)+j)+1) (fun j => intercept.testBit j)
  else if g<ph+k then decide (g-ph<d+1) || !(bit a 0) else equal a

def stageGate (d p start g : ℕ) (first : Bool) (a : W) :=
  let l := linked d; let ps := localPorts (stage d) g a
  let inner := if g<l.ng then linkedGate d g a && stagePins d p ps else if g<l.ng+d+1 then
    let i := g-l.ng; col (d+1) i true a && decide (bit a 2=p.testBit i ∧ (i=d → bit a 0=false)) else equal a
  inner && (!first || pin d ps id (fun j => start.testBit j))
def ordinary (w : W) (g : ℕ) (a : W) :=
  let D := d w; let K := k w; let M := m w; let s := slot D K; let t := stage D; let n := 4*M*s.ng; let endB := n+4*M*t.ng
  let l := (chains M D K).ng; let np := min (pre w).length (4*M*D)
  if g<n then let i := (g/s.ng)%M; let cs := nums (field w 1); slotGate D K (prime w) (threshold w) (cs.getD (2*i) 0-1) (cs.getD (2*i+1) 0) (g%s.ng) a
  else if g<endB then let j := (g-n)/t.ng; stageGate D (prime w) (if j<2*M then target w else 1) ((g-n)%t.ng) (decide (j%(2*M)=0)) a
  else if g<l then equal a else if g<l+np then bit a 0 == bit (pre w) (g-l)
  else if g=l+np then decide ((pre w).length ≤ 4*M*D ∧ bit a 0=false) else equal a
/-- Falling factorial evaluated on natural magnitudes. For -z, use the rising factorial and the parity sign. -/
def magnitude (positive : Bool) (z j : ℕ) := ((List.range j).foldl (fun a i => a*(if positive then z-i else z+i)) 1) / ((List.range j).foldl (fun a i => a*(i+1)) 1)
def coeff (positive : Bool) (z modulus j : ℕ) := let a := magnitude positive z j % modulus
  if !positive && j%2=1 then (modulus-a)%modulus else a
def indicator (n : ℕ) (b : Bool) := encodeNatListBin ((List.range n).map (fun j => if j=0 then b.toNat else 0))
def lookup (w : W) (s : ℕ) (a : W) :=
  let i := s%m w; let bs := blocks w; let l := bs.getD i []; let cs := nums (field w 1); let hash := PolyT.bval a
  let r := l.findIdx (fun x => decide ((cs.getD (2*i) 0*x+cs.getD (2*i+1) 0)%prime w=hash))
  if r<l.length then let z := num (field w 3) (((bs.take i).map List.length).sum+r)
                     encodeNatListBin ((List.range (len w)).map (coeff (decide (2*m w ≤ s)) z (2^prec w)))
  else indicator (len w) false

def fpEntry (z : W) := let w := DetDLP_W1_Queries.first z; let v := PolyT.bval (DetDLP_W1_Queries.second z); let a := DetDLP_W1_Queries.third z
  let c := whole (m w) (d w) (k w) (pre w).length; let ar := c.ng-4*m w
  if v<ar then indicator (len w) (ordinary w v a) else if v<c.ng then lookup w (v-ar) a else indicator (len w) (equal a)

end DetDLP.M3A.FpPolyDefs
abbrev DetDLP_M3A_FpPolyDefs := (DetDLP.M3A.FpPolyDefs.fpBuild,DetDLP.M3A.FpPolyDefs.fpEntry)


