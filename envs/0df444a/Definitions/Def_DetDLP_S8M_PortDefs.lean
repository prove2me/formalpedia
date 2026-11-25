-- Prove2me | Definitions.Def_DetDLP_S8M_PortDefs
-- name    : DetDLP_S8M_PortDefs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T00:38:02.555807+00:00
-- url     : https://prove2.me/theorems/2fbda094-ce5d-4a09-b424-50e5dacd5c73

import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8H_PortCombinators
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.PortPoly
open Groundwork S8H0 S8H.PortCombinators RegisterMap DetDLP_W1_Queries
abbrev W := List Bool
abbrev bit (w : W) (i : ℕ) := w.getD i false
def tab (n : ℕ) (f : ℕ → GC) : GC := let k := (f 0).1; (n*k,fun i => (f (i/k)).2 (i%k))
def tile (n : ℕ) (g : GC) := tab n fun _ => g
def rd (d k : ℕ) : Reader := if k=0 then regR d else pinR (k-1)
def hash (q : List Unit) (d p a x b : ℕ) := genHashG q d p (rd d a) (rd d x) (rd d b)
def atomFixed (q : List Unit) (d p T : ℕ) (c : GateRoutes.Coeff) := catG (catG (tile 16 (rangeG d p)) (catG (manyG 5 fun i => hashG q d p c i.castSucc) (curveG d))) (catG (hash q d p 0 0 0) (catG zeroLastG (rangeG d T)))
def coord (s : W) (b k : ℕ) := PolyT.bval (((s.drop (k*b)).take b).reverse)
def atomG (g : GC) (b d m j : ℕ) (s : W) := catG g (d,fun i w => let k := (j%m)*4+(if bit w 0 then 2 else 0); decide (bit w 1 = (coord s b k).testBit i ∧ bit w 2 = (coord s b (k+1)).testBit i))
def mapG (q : List Unit) (d p b2 a1 a3 : ℕ) := let h := hash q d p; let mask : GC := (d,fun _ w => bit w 1 == (!bit w 0 && bit w 2))
  catG (tile 10 (rangeG d p)) (catG (catG (h (36%p+1) 0 (3*b2%p+1)) (catG (h (a1+1) 0 (a3+1)) (catG (h (2%p+1) 0 0) (h (108%p+1) 0 1)))) (catG (1,fun _ w => bit w 0 == bit w 1) (tile 2 mask)))
def addStepG (q : List Unit) (d p c4term : ℕ) :=
  let g (i : Fin 15) : ℕ × ℕ × ℕ := let n := p-1+1
    ![(n,0,0),(0,0,1),(2,0,0),(0,0,1),(n,0,0),(0,0,1),(0,0,1),(3%p+1,0,c4term+1),(0,0,1),(0,0,1),(n,0,0),(n,0,0),(n,0,0),(0,0,1),(n,0,0)] i
  let inv : GC := (d,fun i w => if bit w 0 then !bit w 1 && !bit w 2 else bit w 3 == (1:ℕ).testBit i)
  let mux : GC := (d,fun _ w => bit w 6 == (if !bit w 0 && !bit w 1 && !bit w 2 then bit w 4 else if !bit w 0 && !bit w 1 && bit w 2 && !bit w 3 then bit w 5 else false))
  let flag : GC := (1,fun _ w => bit w 4 == (if bit w 0 then bit w 1 else !bit w 1 && bit w 2 && bit w 3))
  let dest : GC := (d,fun _ w => bit w 7 == (if bit w 0 then bit w 5 else if bit w 1 then bit w 4 else if bit w 2 && bit w 3 then false else bit w 6))
  catG (tile 34 (rangeG d p)) (catG (manyG 14 fun i => hash q d p (g i).1 (g i).2.1 (g i).2.2) (catG (tile 2 inv) (catG mux (catG flag (tile 2 dest)))))
def foldG (n d : ℕ) (f : Bool) (x y : ℕ) (g : GC) := let eqw (z : ℕ) : GC := (d,fun i w => bit w 0 == z.testBit i)
  catG (1,fun _ w => bit w 0 == f) (catG (eqw x) (catG (eqw y) (tile n g)))
def prime (w : W) := PolyT.bval (first (second w))
def threshold (w : W) := PolyT.bval (third w)
def seed (w : W) := third (more w)
def target (w : W) := third (more (more w))
def prefixBits (w : W) := third (more (more (more w)))
abbrev width := S8G.FpMoment.Code.width
abbrev slots := S8G.FpMoment.Code.slots
def coeff (w : W) : GateRoutes.Coeff := let a := w5_M6Sort.decode (second w); ⟨a.getD 1 0,a.getD 2 0,a.getD 3 0,a.getD 4 0,a.getD 5 0⟩
def bTwo (w : W) := let c := coeff w; (c.a1*c.a1+4*c.a2)%prime w
def cTerm (w : W) := let c := coeff w; let p := prime w; let b := bTwo w; let c4 := (b*b%p+p-(24*(2*c.a4+c.a1*c.a3))%p)%p; (p-(27*c4)%p)%p
def anchorCount (m d e : ℕ) := 2*m*(122*d+14*e+46)+2*m*(70*d+8*e+27)+(2*m-1)*(253*d+30*e+97)+1
def prefixG (n : ℕ) (η : W) : GC := (η.length,fun i v => decide (i<n ∧ bit v 0 = η.getD i false))
def body (w : W) := let p := prime w; let b := width p; let d := b+1; let m := slots b; let q := CoreCheck.pad p; let c := coeff w; let t := w5_M6Sort.decode (target w); let f := decide (t.getD 0 0 = 1); let x := t.getD 1 0; let y := t.getD 2 0
  let a := atomFixed q d p (threshold w) c; let η := prefixBits w
  catG (anchorsG (anchorCount m d (S8H.PointAddresses.wires d))) (catG zeroLastG (catG (tab (2*m) fun j => atomG a b d m j (seed w)) (catG (tile (2*m) (mapG q d p (bTwo w) c.a1 c.a3)) (catG (foldG (2*m-1) d f (if t.getD 0 0 = 1 then 0 else (36*x+3*bTwo w)%p) (if t.getD 0 0 = 1 then 0 else (108*(2*y+c.a1*x+c.a3))%p) (addStepG q d p (cTerm w))) (prefixG (2*m*(2*b+1)) η)))))
def port := fullPort body
end DetDLP.S8M.PortPoly


