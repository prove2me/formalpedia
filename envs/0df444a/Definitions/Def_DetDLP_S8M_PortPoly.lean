-- Prove2me | Definitions.Def_DetDLP_S8M_PortPoly
-- name    : DetDLP_S8M_PortPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T00:29:36.677619+00:00
-- url     : https://prove2.me/theorems/6a18e944-3e7a-4503-97c7-bb5f297f5f29
-- title:
--   Tag 6 pure-GC port evaluator and PolyT bound
-- statement:
--   **Definition.** For a tag-6 packet $w$, `body w` specifies a gate count and a Boolean predicate indexed by a gate address and its incident bits. The gate order is anchors, the zero check, $2m$ atom slots, $2m$ coordinate maps, fold output checks, $2m-1$ additions, and the prefix rows. Within equal-sized tiles of length $k>0$, address $i$ selects tile $\lfloor i/k\rfloor$ and local gate $i\bmod k$.
--
--   **Bound.** `body_poly` proves polynomial-time evaluation of both the gate count and the addressed predicate. Applying `fullPort_poly` to this result gives `port_poly : PolyT port` for the encoded port query.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8H_PortCombinators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.PortPoly
open Groundwork S8H0 S8H.PortCombinators RegisterMap DetDLP_W1_Queries
abbrev W := List Bool
abbrev bit (w : W) (i : ℕ) := w.getD i false
/-- Equal-size tiles: the quotient selects the copy and the remainder its local gate. -/
def tab (n : ℕ) (f : ℕ → GC) : GC := let k := (f 0).1; (n*k,fun i => (f (i/k)).2 (i%k))
def tile (n : ℕ) (g : GC) := tab n fun _ => g
-- Operand code zero denotes a register; the successor of k denotes the public word k.
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
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.length PolyT.getD PolyT.testBit PolyT.decide_lt PolyT.decide_eq PolyT.div PolyT.mod CoreCheck.reorder_poly CoreCheck.column_poly CoreCheck.pad_poly w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly w4_M5Evaluator.clog2_poly S8G.FpMoment.Code.width_poly S8G.FpMoment.Code.slots_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 PolyT.drop PolyT.take PolyT.reverse w5_M6Sort.decode_poly first_poly more_poly
@[local fun_prop] theorem prime_poly : PolyT prime := by unfold prime second; fun_prop
@[local fun_prop] theorem threshold_poly : PolyT threshold := by unfold threshold third second; fun_prop
@[local fun_prop] theorem seed_poly : PolyT seed := by unfold seed third second; fun_prop
@[local fun_prop] theorem target_poly : PolyT target := by unfold target third second; fun_prop
@[local fun_prop] theorem prefix_poly : PolyT prefixBits := by unfold prefixBits third second; fun_prop
variable {α β : Type} [Enc α] [Enc β]
private theorem pull {F : β → GC} {u : α → β} (hf : EffG F) (hu : PolyT u) : EffG fun x => F (u x) := by
  have h := PolyT.comp hf.1 hu; have k := PolyT.comp hf.2 (PolyT.prodMk (PolyT.comp hu (PolyT.fst (PolyT.id' (α:=α × ℕ × W)))) (PolyT.snd PolyT.id')); exact ⟨h,k⟩
private theorem tabP {n : α → ℕ} {F : α → ℕ → GC} (hn : PolyT n) (h : EffG fun z : α × ℕ => F z.1 z.2) : EffG fun x => tab (n x) (F x) := by
  have hk := PolyT.comp h.1 (PolyT.prodMk PolyT.id' (PolyT.const 0)); have k := PolyT.comp hk (PolyT.fst (PolyT.id' (α:=α × ℕ × W))); have i := PolyT.fst (PolyT.snd (PolyT.id' (α:=α × ℕ × W)))
  exact ⟨PolyT.mul hn hk,PolyT.comp h.2 (PolyT.prodMk (PolyT.prodMk (PolyT.fst PolyT.id') (PolyT.div i k)) (PolyT.prodMk (PolyT.mod i k) (PolyT.snd (PolyT.snd PolyT.id'))))⟩
private theorem tileP {n : α → ℕ} {F : α → GC} (hn : PolyT n) (h : EffG F) : EffG fun x => tile (n x) (F x) := tabP hn (pull h (PolyT.fst PolyT.id'))
variable {q : α → List Unit} {d p a x b : α → ℕ}
private theorem hashP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (ha : PolyT a) (hx : PolyT x) (hb : PolyT b) : EffG fun z => hash (q z) (d z) (p z) (a z) (x z) (b z) := by
  unfold hash genHashG prodG; refine catG_poly (catG_poly (catG_poly ?_ ?_) (catG_poly ?_ ?_)) (catG_poly ?_ (catG_poly ?_ ?_))
  all_goals constructor <;> simp only [mulG,eqsG,addG,rd,ite_apply,regR,pinR] <;> fun_prop (disch := assumption)
private theorem rangeP (hd : PolyT d) (hp : PolyT p) : EffG fun z => rangeG (d z) (p z) := by constructor <;> simp only [rangeG,addG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem fixedP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) {t : α → ℕ} (ht : PolyT t) {c : α → GateRoutes.Coeff} (h1 : PolyT fun z => (c z).a1) (h2 : PolyT fun z => (c z).a2) (h3 : PolyT fun z => (c z).a3) (h4 : PolyT fun z => (c z).a4) (h6 : PolyT fun z => (c z).a6) : EffG fun z => atomFixed (q z) (d z) (p z) (t z) (c z) := by
  refine catG_poly (catG_poly (tileP (PolyT.const 16) (rangeP hd hp)) (catG_poly (many_poly fun i => hash_poly i.castSucc hq hd hp h1 h2 h3 h4 h6) ?_)) (catG_poly (hashP hq hd hp (PolyT.const 0) (PolyT.const 0) (PolyT.const 0)) (catG_poly ?_ (rangeP hd ht)))
  all_goals constructor <;> simp only [curveG,CurveRows.test,zeroLastG] <;> fun_prop (disch := assumption)
private theorem mapP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (hb : PolyT b) (ha : PolyT a) (hx : PolyT x) : EffG fun z => mapG (q z) (d z) (p z) (b z) (a z) (x z) := by
  refine catG_poly (tileP (PolyT.const 10) (rangeP hd hp)) (catG_poly (catG_poly ?_ (catG_poly ?_ (catG_poly ?_ ?_))) (catG_poly ?_ (tileP (PolyT.const 2) ?_)))
  iterate 4 (refine hashP hq hd hp ?_ ?_ ?_ <;> fun_prop (disch := assumption))
  all_goals constructor <;> dsimp only [bit] <;> fun_prop (disch := assumption)
private theorem stepP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (ha : PolyT a) : EffG fun z => addStepG (q z) (d z) (p z) (a z) := by
  refine catG_poly (tileP (PolyT.const 34) (rangeP hd hp)) (catG_poly (many_poly fun i => ?_) (catG_poly (tileP (PolyT.const 2) ?_) (catG_poly ?_ (catG_poly ?_ (tileP (PolyT.const 2) ?_)))))
  · apply hashP hq hd hp <;> fin_cases i <;> simp <;> fun_prop (disch := assumption)
  all_goals constructor <;> dsimp only [bit] <;> fun_prop (disch := assumption)
private theorem foldP {n : α → ℕ} {f : α → Bool} {g : α → GC} (hn : PolyT n) (hd : PolyT d) (hf : PolyT f) (hx : PolyT x) (hy : PolyT b) (hg : EffG g) : EffG fun z => foldG (n z) (d z) (f z) (x z) (b z) (g z) := by
  refine catG_poly ?_ (catG_poly ?_ (catG_poly ?_ (tileP hn hg))); all_goals constructor <;> dsimp only [bit] <;> fun_prop (disch := assumption)
private theorem atomP {s : α → W} {m j : α → ℕ} {F : α → GC} (hg : EffG F) (hb : PolyT b) (hd : PolyT d) (hm : PolyT m) (hj : PolyT j) (hs : PolyT s) : EffG fun z => atomG (F z) (b z) (d z) (m z) (j z) (s z) := by
  refine catG_poly hg ?_; constructor <;> dsimp only [bit,coord] <;> fun_prop (disch := assumption)
private theorem prefixP {n : α → ℕ} {e : α → W} (hn : PolyT n) (he : PolyT e) : EffG fun z => prefixG (n z) (e z) := by constructor <;> dsimp only [prefixG,bit] <;> fun_prop (disch := assumption)
theorem body_poly : EffG body := by
  have hp := prime_poly; have hb := S8G.FpMoment.Code.width_poly hp; have hd := PolyT.add hb (PolyT.const 1); have hm := S8G.FpMoment.Code.slots_poly hb; have he := S8H.PointAddresses.mul_poly.nb hd; have hq := CoreCheck.pad_poly hp
  have hc (k : ℕ) : PolyT (fun w : W => (w5_M6Sort.decode (second w)).getD k 0) := by unfold second; fun_prop
  have H := fixedP (c:=coeff) hq hd hp threshold_poly (hc 1) (hc 2) (hc 3) (hc 4) (hc 5)
  have h2 : PolyT bTwo := by unfold bTwo; dsimp only [coeff,second]; fun_prop
  have ht : PolyT cTerm := by unfold cTerm; dsimp only [coeff,second]; fun_prop (disch := assumption)
  have hn := PolyT.mul (PolyT.const 2) hm; have pi := PolyT.fst (PolyT.id' (α:=W × ℕ)); have hj := PolyT.snd (PolyT.id' (α:=W × ℕ))
  have hh := atomP (pull H pi) (PolyT.comp hb pi) (PolyT.comp hd pi) (PolyT.comp hm pi) hj (PolyT.comp seed_poly pi)
  have hat := tabP (F:=fun w j => let p := prime w; let b := width p; let d := b+1; atomG (atomFixed (CoreCheck.pad p) d p (threshold w) (coeff w)) b d (slots b) j (seed w)) hn hh
  let t := fun w => w5_M6Sort.decode (target w); have tv (k : ℕ) : PolyT (fun w => (t w).getD k 0) := by dsimp [t]; fun_prop
  let f := fun w => decide ((t w).getD 0 0 = 1); have hf : PolyT f := by dsimp [f]; exact PolyT.decide_eq (tv 0) (PolyT.const 1)
  have tx := PolyT.ite' hf (PolyT.const 0) (PolyT.mod (PolyT.add (PolyT.mul (PolyT.const 36) (tv 1)) (PolyT.mul (PolyT.const 3) h2)) hp)
  have ty := PolyT.ite' hf (PolyT.const 0) (PolyT.mod (PolyT.mul (PolyT.const 108) (PolyT.add (PolyT.add (PolyT.mul (PolyT.const 2) (tv 2)) (PolyT.mul (hc 1) (tv 1))) (hc 3))) hp)
  have fold := foldP (PolyT.sub hn (PolyT.const 1)) hd hf tx ty (stepP hq hd hp ht)
  have ha : PolyT (fun w => anchorCount (slots (width (prime w))) (width (prime w)+1) (S8H.PointAddresses.wires (width (prime w)+1))) := by unfold anchorCount; fun_prop (disch := assumption)
  have pre := PolyT.mul hn (PolyT.add (PolyT.mul (PolyT.const 2) hb) (PolyT.const 1)); have hbits := PolyT.snd (PolyT.snd (PolyT.id' (α:=W × ℕ × W)))
  have hpre := prefixP pre prefix_poly
  have tail := catG_poly fold hpre
  have maps := tileP hn (mapP hq hd hp h2 (hc 1) (hc 3))
  have net := catG_poly hat (catG_poly maps tail)
  have ans := catG_poly (show EffG (fun w => anchorsG (anchorCount (slots (width (prime w))) (width (prime w)+1) (S8H.PointAddresses.wires (width (prime w)+1)))) from ⟨ha,PolyT.const true⟩) (catG_poly (show EffG (fun _ : W => zeroLastG) from ⟨PolyT.const 1,PolyT.not' (PolyT.getD hbits (PolyT.const 0) (PolyT.const false))⟩) net)
  exact ans
theorem port_poly : PolyT port := fullPort_poly body_poly
end DetDLP.S8M.PortPoly


