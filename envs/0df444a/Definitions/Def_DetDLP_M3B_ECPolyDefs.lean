-- Prove2me | Definitions.Def_DetDLP_M3B_ECPolyDefs
-- name    : DetDLP_M3B_ECPolyDefs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T21:54:57.074015+00:00
-- url     : https://prove2.me/theorems/c8e2c700-6d9a-4e7d-b599-74b561045457
-- title:
--   Numeric programs for native elliptic-curve wire packets and entries
-- statement:
--   Total bit-list programs specifying the EC packet builder and local ring entry evaluator, including numeric incidence and lookup addresses.
-- source:
--   Deterministic Discrete Logarithms, Section 4.2, pp. 14–15.

import Definitions.Def_DetDLP_S8H_PointAddresses
import Definitions.Def_DetDLP_S8H_WirePacket
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_W4_M5Dispatch

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace DetDLP.M3B.ECPolyDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev W := List Bool
abbrev Bit := ℕ × Bool × Bool
abbrev Word := ℕ → Bit
abbrev XYZ := Bit × Word × Word
abbrev N := ℕ × ℕ × (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → W → Bool)
def ng (a : N) := a.1
def ne (a : N) := a.2.1
def gate (a : N) := a.2.2.1
def signal (a : N) := a.2.2.2.1
def check (a : N) := a.2.2.2.2
def noneN : N := (0,0,id,id,fun _ _ => false)
def cat (a b : N) : N := (ng a+ng b, ne a+ne b,
  fun j => if j<ne a then gate a j else ng a+gate b (j-ne a),
  fun j => if j<ne a then signal a j else signal b (j-ne a),
  fun j => if j<ng a then check a j else check b (j-ng a))
/-- Repetition of fixed-size blocks whose addresses and tests may depend on the index. -/
def copies (n : ℕ) (f : ℕ → N) : N :=
  let g := ng (f 0); let e := ne (f 0)
  (n*g,n*e, fun j => j/e*g+gate (f (j/e)) (j%e), fun j => signal (f (j/e)) (j%e), fun j => check (f (j/g)) (j%g))
def pin (dummy : ℕ) (b : Bool) : Bit := (dummy,b,b)
def reg (j : ℕ) : Bit := (j,false,true)
def mask (j : ℕ) (b : Bool) : Bit := (j,false,b)
def rd (r : Bit) (x : Bool) := if x then r.2.2 else r.2.1
def pub (K n : ℕ) : Word := fun j => pin K (n.testBit j)
def word (K off n : ℕ) : Word := fun j => if j<n then reg (off+j) else pin K false
def rows (n m : ℕ) (w : ℕ → ℕ → Bit) (test : ℕ → (ℕ → Bool) → Bool) : N :=
  (n,n*m,fun e => e/m,fun e => (w (e/m) (e%m)).1,fun i l => test i (fun j => rd (w i j) (l.getD j false)))
def eqs (n : ℕ) (a b : Word) := rows n 2 (fun i j => if j=0 then a i else b i) (fun _ v => v 0 == v 1)
def col (n : ℕ) (cin : Bool) (x y z c : Word) : N :=
  let ref := fun i j => match j with | 0 => x i | 1 => y i | 2 => z i | 3 => c i | _ => c (if i=0 then n-1 else i-1)
  rows n 5 ref fun i v => decide ((v 0).toNat+(v 1).toNat+(if i=0 then cin else v 4).toNat=(v 2).toNat+2*(v 3).toNat ∧ (i+1=n → v 3=false))
def prod (K d off : ℕ) (a b z : Word) : N :=
  let m := S8H.PointAddresses.mul d; let e := m.nb
  let u : N := (m.ng,m.ne,m.gate,fun j => off+m.bit j, fun g l =>
    let ps := (List.range e).filter (fun j => decide (w4_M5EdgeNat.srcNat d j=g ∨ w4_M5EdgeNat.dstNat d j=g))
    let ls := ps.filter fun j => decide (w4_M5EdgeNat.srcNat d j=g)
    let rs := ps.filter fun j => decide (w4_M5EdgeNat.srcNat d j≠g)
    w4_M5Dispatch.evalNat (List.replicate d ()) g (ps.map fun j => l.getD ((ls++rs).idxOf j) false))
  cat u (eqs (4*d) (fun j => reg (off+(if j<2*d then j else e-2*d+(j-2*d))))
    (fun j => if j<d then a j else if j<2*d then b (j-d) else z (j-2*d)))
def triple (d : ℕ) := 3*d+1
def pt (d : ℕ) := 1+2*triple d
def run (d e : ℕ) := 2*triple d+d+2*(2*d+e)+1
def aux (d : ℕ) := 2*d+3*(d+1)
def gsize (d e : ℕ) := run d e+aux d
def ptw (K d t : ℕ) : XYZ := (reg t,word K (t+1) d,word K (t+1+triple d) d)
def bnd (K p d t : ℕ) := col (d+1) true (word K t d) (word K (t+d) d) (pub K p) (fun j => reg (t+2*d+j))
def pbound (K p d t : ℕ) := cat (bnd K p d (t+1)) (bnd K p d (t+1+triple d))
def gbound (K p d t : ℕ) := cat (bnd K p d t) (bnd K p d (t+triple d))
def hash (K p d e r ax : ℕ) (a x b : Word) : N :=
  let rem := r+triple d; let q := rem+triple d; let u := q+d; let v := u+2*d+e; let cp := v+2*d+e
  let w := word K; let sum := w (ax+2*d) (d+1)
  cat (cat (prod K d (u+2*d) a x (w u (2*d))) (prod K d (v+2*d) (w q d) (pub K p) (w v (2*d))))
    (cat (col (2*d) false (w v (2*d)) (w rem d) (w u (2*d)) (fun j => reg (ax+j)))
      (cat (col (d+1) false (w rem d) b sum (fun j => reg (ax+3*d+1+j)))
        (col (d+1) false (w r d) (fun j => mask cp (p.testBit j)) sum (fun j => reg (ax+4*d+2+j)))))
def ghash (K p d e t : ℕ) (args : Word × Word × Word) := hash K p d e t (t+run d e) args.1 args.2.1 args.2.2
def mapSize (d e : ℕ) := pt d+4*gsize d e
def addSize (d e : ℕ) := pt d+2*(1+triple d)+d+15*gsize d e
def mapN (K p d e t : ℕ) (q : XYZ) :=
  let go := fun j => t+pt d+j*gsize d e; let res := fun j => word K (go j) d
  let A : ℕ → Word × Word × Word := fun j => match j with
    | 0 => (pub K (36%p),q.2.1,pub K 0) | 1 => (pub K 0,q.2.1,pub K 0)
    | 2 => (pub K (2%p),q.2.2,res 1) | _ => (pub K (108%p),res 2,pub K 0)
  let cmp := fun (o g : Word) => rows d 3 (fun i j => match j with | 0 => q.1 | 1 => o i | _ => g i) (fun _ v => v 1 == (!v 0 && v 2))
  cat (cat (pbound K p d t) (copies 4 fun j => gbound K p d (go j)))
    (cat (copies 4 fun j => ghash K p d e (go j) (A j))
      (cat (eqs 1 (fun _ => reg t) (fun _ => q.1)) (cat (cmp (ptw K d t).2.1 (res 0)) (cmp (ptw K d t).2.2 (res 3)))))
def addN (K p d e t c4 : ℕ) (P Q : XYZ) :=
  let cp := fun j => t+pt d+j*(1+triple d); let a := fun j => word K (cp j+1) d; let b := fun j => reg (cp j)
  let off := cp 2; let l := word K off d; let go := fun j => off+d+j*gsize d e; let g := fun j => word K (go j) d
  let m := pub K (p-1); let one := pub K 1; let zero := pub K 0; let x := P.2.1; let y := P.2.2; let z := Q.2.1; let w := Q.2.2
  let A : ℕ → Word × Word × Word := fun k => match k with
    | 0 => (m,x,z) | 1 => (g 0,a 0,zero) | 2 => (one,y,w) | 3 => (g 2,a 1,zero) | 4 => (m,y,w)
    | 5 => (g 4,a 0,zero) | 6 => (x,x,zero) | 7 => (pub K 3,g 6,pub K c4) | 8 => (g 7,a 1,zero)
    | 9 => (l,l,zero) | 10 => (m,x,g 9) | 11 => (m,z,g 10) | 12 => (m,g 11,x) | 13 => (l,g 12,zero) | _ => (m,y,g 13)
  let inv := fun j => rows d 5 (fun k h => match h with | 0 => b j | 1 => g (2*j) k | 2 => a j k | 3 => g (2*j+1) k | _ => one k)
    (fun _ v => if v 0 then !v 1 && !v 2 else v 3 == v 4)
  let br := fun (n : ℕ) (o u v g h : Word) (slope : Bool) => rows n 9
    (fun k j => match j with | 0 => P.1 | 1 => Q.1 | 2 => b 0 | 3 => b 1 | 4 => o k | 5 => u k | 6 => v k | 7 => g k | _ => h k)
    (fun _ v => v 4 == (if slope then (if !v 0 && !v 1 && !v 2 then v 5 else if !v 0 && !v 1 && v 2 && !v 3 then v 6 else v 7)
      else if v 0 then v 5 else if v 1 then v 6 else if v 2 && v 3 then v 7 else v 8))
  cat (cat (pbound K p d t) (cat (copies 2 fun j => bnd K p d (cp j+1)) (copies 15 fun j => gbound K p d (go j))))
    (cat (copies 15 fun j => ghash K p d e (go j) (A j)) (cat (inv 0) (cat (inv 1)
      (cat (br d l (g 5) (g 8) zero zero true) (cat (br 1 (fun _ => reg t) (fun _ => Q.1) zero one zero false)
        (cat (br d (ptw K d t).2.1 z x zero (g 11) false) (br d (ptw K d t).2.2 w y zero (g 14) false)))))))
def chainSize (d e m : ℕ) := (2*m+1)*mapSize d e+2*m*addSize d e
def bankSize (d e : ℕ) := pt d+7*run d e+7*aux d
def slotSize (d e w : ℕ) := bankSize d e+d+(d+1)+3*w
def select (K a b pos neg : ℕ) : Word := fun j =>
  match a.testBit j,b.testBit j with | false,true => reg pos | true,false => reg neg | x,_ => pin K x

def slotN (K p d e w t T : ℕ) (cs seed : List ℕ) (b : ℕ) :=
  let X := word K (t+1) d; let yo := t+1+triple d; let Y := word K yo d
  let r := fun g => t+pt d+g*run d e; let ax := fun g => r 7+g*aux d; let g := fun i => word K (r i) d
  let u := fun z => pub K (cs.getD z 0); let pub := pub K
  let pick := fun l => select K (seed.getD (4*b+l) 0) (seed.getD (4*b+2+l) 0) yo t
  let A : ℕ → Word × Word × Word := fun i => match i with
    | 0 => (u 1,X,Y) | 1 => (pub 1,g 0,u 3) | 2 => (g 1,Y,pub 0) | 3 => (pub 1,X,u 2)
    | 4 => (g 3,X,u 4) | 5 => (g 4,X,u 5) | _ => (pick 0,X,pick 1)
  let diff := t+bankSize d e
  cat (rows 1 1 (fun _ _ => reg K) (fun _ v => !v 0))
    (cat (cat (pbound K p d t) (copies 7 (fun i => gbound K p d (r i))))
     (cat (rows 1 2 (fun _ j => reg (if j=0 then yo else t)) (fun _ v => v 1 == !v 0))
     (cat (copies 7 (fun i => hash K p d e (r i) (ax i) (A i).1 (A i).2.1 (A i).2.2))
     (cat (eqs d (g 2) (g 5)) (col (d+1) true (g 6) (word K diff d) (pub T) (fun j => reg (diff+d+j)))))))
def busOff (d e w i j : ℕ) := i*slotSize d e w+bankSize d e+d+(d+1)+j*w
def busN (K d e w T i : ℕ) :=
  let t := i*slotSize d e w; let parity := reg (t+1+triple d)
  let h := word K (t+pt d+6*run d e) d
  let b := fun j => word K (busOff d e w i j) w
  cat (rows w 2 (fun j l => if l=0 then parity else b 0 j) (fun j v => v 1 == (v 0 && T.testBit j)))
    (col w false h (b 0) (b 1) (b 2))
def frames (w : W) := (w.foldl (fun (c : List W × W) _ => if c.2.headD false then
  ((DetDLP_W1_Queries.first c.2).take w.length :: c.1,(DetDLP_W1_Queries.more c.2).take w.length) else c) ([],w)).1.reverse
def net (cs seed point : List ℕ) (pre : W) (m k T : ℕ) : N :=
  let p := cs.getD 0 0; let d := bitLen p+1; let w := max d k; let e := S8H.PointAddresses.wires d
  let t := fun i => i*slotSize d e w; let ch := fun s => t (4*m)+s*chainSize d e m
  let term := ch 2; let K := term+pt d
  let factor := fun i => (pin K false,(ptw K d (t i)).2)
  let chain := fun s =>
    let mp := fun i => ch s+i*mapSize d e; let ad := fun i => mp (2*m+1)+i*addSize d e
    let acc := fun i => if i=0 then mp 0 else ad (i-1)
    let init : XYZ := if s=1 then (pin K true,pub K 0,pub K 0) else
      (pin K (decide (point.getD 0 0=1)),pub K (point.getD 1 0),pub K (point.getD 2 0))
    let c4 := (1296*(cs.getD 4 0))%p
    cat (copies (2*m+1) (fun i => mapN K p d e (mp i) (if i=0 then init else factor (2*(i-1)+s))))
      (cat (copies (2*m) (fun i => addN K p d e (ad i) c4 (ptw K d (acc i)) (ptw K d (mp (i+1)))))
       (eqs (pt d) (word K (acc (2*m)) (pt d)) (word K term (pt d))))
  let b := d-1; let count := 4*m*(3*b)
  let pref := if pre.length ≤ count then rows pre.length 1 (fun j _ =>
    let s := j/(2*m*(3*b)); let i := (j/(3*b))%(2*m); let h := (j/b)%3
    if h=0 then pin K false else if h=1 then (factor (2*i+s)).2.1 (j%b) else (factor (2*i+s)).2.2 (j%b))
    (fun j v => v 0 == pre.getD j false) else rows 1 1 (fun _ _ => pin K false) (fun _ _ => false)
  cat (rows (K+1) 1 (fun i _ => reg i) (fun _ _ => true))
    (cat (copies (4*m) (fun i => slotN K p d e w (t i) T cs seed (i/4))) (cat (chain 0) (cat (chain 1) (cat (copies (4*m) (busN K d e w T)) pref))))

def dimensions (w : W) :=
  let fs := frames w; let ns := fun n => w5_M6Sort.decode (fs.getD n [])
  let b := bitLen ((ns 0).getD 0 0); let m := (ns 3).length/4; let T := (ns 2).getD 1 0; let M := (ns 2).getD 0 0
  let k := Nat.clog 2 (2*T); let prec := 2+4*m*k+(8*m+2)*Nat.clog 2 (4*m*M+2)
  (b,m,k,T,prec,8*m+3)
def compiled (w : W) :=
  let fs := frames w; let ns := fun n => w5_M6Sort.decode (fs.getD n [])
  let dims := dimensions w
  net (ns 0) (ns 3) (ns 1) (fs.getD 6 []) dims.2.1 dims.2.2.1 dims.2.2.2.1

def succWire (a : N) (i : ℕ) :=
  let l := (List.range (ne a)).filter fun j => decide (signal a j = signal a i)
  l.getD ((l.idxOf i+1)%l.length) i

def ecBuild (w : W) : W :=
  let dims := dimensions w; let b := dims.1; let d := b+1; let e := S8H.PointAddresses.wires d
  let m := dims.2.1; let k := dims.2.2.1; let a := compiled w
  let n := ne a; let g := ng a; let lookup := g+n; let nG := lookup+4*m; let nV := nG+n; let nE := 3*n+4*m*k
  let src := fun i => if i<n then gate a i else if i<3*n then g+(i-n)%n else lookup+(i-3*n)/k
  let dst := fun i => nG+(if i<n then i else if i<2*n then i-n else if i<3*n then succWire a (i-2*n) else
    busOff d e (max d k) ((i-3*n)/k) 1 + (i-3*n)%k)
  Encoding.encodeList id [w,S8H.WirePacket.packet nV nE src dst,countWord b,countWord m,countWord k,countWord (100000000*m*b),
    countWord dims.2.2.2.2.1,countWord dims.2.2.2.2.2,(List.range (nV+nE)).map (fun j => decide (lookup ≤ j ∧ j<nG))]

def lookup (fs : List W) (T i h : ℕ) : Option ℕ :=
  let B := (frames (fs.getD 4 [])).map frames; let block := B.getD i []
  let cs := w5_M6Sort.decode (fs.getD 0 []); let p := cs.getD 0 0; let seed := w5_M6Sort.decode (fs.getD 3 [])
  let lbl := w5_M6Sort.decode (fs.getD 5 []); let off := ((B.take i).map List.length).sum
  let addr := fun l =>
    let point := w5_M6Sort.decode l; let s := point.getD 2 0 % 2; let j := 4*i+2*s
    if point.getD 0 0 = 1 then 2*T else ((seed.getD j 0)*(point.getD 1 0)+seed.getD (j+1) 0)%p+s*T
  ((List.range block.length).find? (fun j => decide (addr (block.getD j []) = h))).map fun j => lbl.getD (off+j) 0

def ecEntry (q : W) : W :=
  let w := DetDLP_W1_Queries.first q; let v := Groundwork.PolyT.bval (DetDLP_W1_Queries.second q); let l := DetDLP_W1_Queries.third q
  let dims := dimensions w; let m := dims.2.1; let a := compiled w; let n := ne a; let g := ng a; let lookup0 := g+n
  let prec := dims.2.2.2.2.1; let len := dims.2.2.2.2.2
  let ind := fun (ok : Bool) => encodeNatListBin ((List.range len).map (fun j => if ok && j=0 then 1 else 0))
  if v<g then ind (check a v l) else if lookup0 ≤ v ∧ v<lookup0+4*m then
    let i := v-lookup0
    match lookup (frames w) dims.2.2.2.1 (i/4) (Groundwork.PolyT.bval l) with
    | none => ind false
    | some z => let x : ℤ := if i%2=1 then (z:ℤ) else -(z:ℤ)
                encodeNatListBin ((List.range len).map (fun j => (Ring.choose x j % (2^prec:ℤ)).toNat))
  else ind (l.all (· == true) || l.all (· == false))
end DetDLP.M3B.ECPolyDefs


