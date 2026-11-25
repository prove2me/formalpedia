-- Prove2me | Definitions.Def_DetDLP_S8G_PortPoly
-- name    : DetDLP_S8G_PortPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:56:09.606828+00:00
-- url     : https://prove2.me/theorems/9f2e12e5-79d3-475b-84cd-4fa969c3cf06
-- title:
--   Tag 1 four-branch port evaluator and fast PolyT bound
-- statement:
--   For a tag-1 descriptor with branch $j\in\{0,1,2,3\}$, the local evaluator uses $\min(j,2)$ atom banks and a product check exactly when $j=3$. Repetition of a gate block of size $g$ uses the local address $i\bmod g$, so the evaluator need not enumerate the bank. The module proves polynomial-time bounds for the local Boolean predicate and its encoded port query.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H_PortCombinators
import Definitions.Def_DetDLP_S8G_AnchoredBank
import Definitions.Def_DetDLP_S8G_FpMomentPoly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8G.PortPoly
open S8H0 S8H.PortCombinators RegisterMap SeedAndAtomBank Routes FpAtomRows Groundwork FpMoment.Code
abbrev W := List Bool
/-- Random access to identical consecutive gate blocks, including zero copies. -/
def tile (n : ℕ) (g : GC) : GC := (n*g.1, fun i => g.2 (i%g.1))
def seedG (d p : ℕ) := catG (rangeG d (p-1)) (catG (rangeG d p) (addG (d+1) false (regR d) (pinR 1) (regR d)))
def orG (n : ℕ) (first : Bool) : GC := (n+1,fun i w => if i<n then decide (w.getD 2 false = (((i != 0 || first) && w.getD 0 false) || w.getD 1 false)) else (i != 0 || first) && w.getD 0 false)
def atomG (q : List Unit) (d p T : ℕ) := let r := rangeG d p; let w := regR d
  catG r (catG (orG d false) (catG r (catG (rangeG d T) (catG r (genHashG q d p w w w)))))
def stageG (q : List Unit) (d p : ℕ) := let r := regR d; let z := regR (2*d)
  catG (catG (prodG q d r r z) (prodG q d r (pinR p) z)) (addG (2*d) false z r z)
def anchorCount (c o m d e : ℕ) := (seedShape m d).size+c*(atomBankShape m d e).size+o*((triple d).size+c*(chainShape (m-1) d e).size)+1
def tree (q : List Unit) (b m p T c o e : ℕ) (η : W) := let d := b+1
  let pre := rowsG η.length 1 (fun _ _ x => x) fun i f => decide (i < m*2*b ∧ f 0 = η.getD i false)
  let chain := catG (0,fun _ _ => false) (catG (tile (m-1-1) (rangeG d p)) (tile (m-1) (stageG q d p)))
  catG (anchorsG (anchorCount c o m d e)) (catG zeroLastG (catG (catG (tile m (seedG d p)) pre)
    (catG (tile c (tile m (atomG q d p T))) (tile o (catG (rangeG d p) (tile c chain))))))
def decoded (w : W) := let p := prime w; let b := width p; let j := idx w
  tree (CoreCheck.pad p) b (slots b) p (threshold w) (min j 2) (if j=3 then 1 else 0) (S8H.PointAddresses.wires (b+1)) (pfx w)
/-- Local gate predicate of the descriptor at a zero-based gate address. -/
def port (w : W) : ℕ → W → Bool := (decoded w).2
abbrev packetPort := fullPort decoded
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.testBit PolyT.getD PolyT.decide_lt PolyT.decide_eq CoreCheck.reorder_poly CoreCheck.column_poly w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly w4_M5Evaluator.clog2_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
private abbrev Row := W × ℕ × W
private theorem hx : PolyT (@Prod.fst W (ℕ × W)) := PolyT.fst PolyT.id'
private theorem hi : PolyT (fun z : Row => z.2.1) := PolyT.fst (PolyT.snd PolyT.id')
private theorem hw : PolyT (fun z : Row => z.2.2) := PolyT.snd (PolyT.snd PolyT.id')
private theorem bit (k : ℕ) : PolyT (fun z : Row => z.2.2.getD k false) := PolyT.getD hw (PolyT.const k) (PolyT.const false)
private theorem tileP {N : W → ℕ} {F : W → GC} (hn : PolyT N) (h : EffG F) : EffG fun x => tile (N x) (F x) :=
  ⟨PolyT.mul hn h.1, PolyT.comp h.2 (PolyT.prodMk hx (PolyT.prodMk (PolyT.mod hi (PolyT.comp h.1 hx)) hw))⟩
variable {Q : W → List Unit} {D P T : W → ℕ}
private theorem rangeP (hd : PolyT D) (hp : PolyT P) : EffG fun x => rangeG (D x) (P x) := by
  constructor <;> simp only [rangeG,addG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem seedP (hd : PolyT D) (hp : PolyT P) : EffG fun x => seedG (D x) (P x) := by
  refine catG_poly (rangeP hd (PolyT.sub hp (PolyT.const 1))) (catG_poly (rangeP hd hp) ?_)
  constructor <;> simp only [addG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem orP (hd : PolyT D) : EffG fun x => orG (D x) false := by
  have hb : PolyT (fun z : Row => (z.2.1 != 0 || false) && z.2.2.getD 0 false) := by fun_prop (disch := assumption)
  exact ⟨PolyT.add hd (PolyT.const 1),PolyT.ite' (PolyT.decide_lt hi (PolyT.comp hd hx)) (PolyT.decide_eq (bit 2) (PolyT.or' hb (bit 1))) hb⟩
private theorem hashP (hq : PolyT Q) (hd : PolyT D) (hp : PolyT P) : EffG fun x => genHashG (Q x) (D x) (P x) (regR (D x)) (regR (D x)) (regR (D x)) := by
  unfold genHashG prodG; refine catG_poly (catG_poly (catG_poly ?_ ?_) (catG_poly ?_ ?_)) (catG_poly ?_ (catG_poly ?_ ?_))
  all_goals constructor <;> simp only [mulG,eqsG,addG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem stageP (hq : PolyT Q) (hd : PolyT D) (hp : PolyT P) : EffG fun x => stageG (Q x) (D x) (P x) := by
  unfold stageG prodG; refine catG_poly (catG_poly (catG_poly ?_ ?_) (catG_poly ?_ ?_)) ?_
  all_goals constructor <;> simp only [mulG,eqsG,addG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem anchorsP {C O M E : W → ℕ} (hc : PolyT C) (ho : PolyT O) (hm : PolyT M) (hd : PolyT D) (he : PolyT E) : EffG fun x => anchorsG (anchorCount (C x) (O x) (M x) (D x) (E x)) := by
  refine ⟨?_,PolyT.const true⟩; simp only [anchorsG,anchorCount,seedShape,seedSlot,atomBankShape,atomSlot,chainShape,stageShape,run,triple,RegisterMap.mul,GateRoutes.auxShape,Shape.size]; fun_prop (disch := assumption)
private theorem preP {M B : W → ℕ} (hm : PolyT M) (hb : PolyT B) : EffG fun x => rowsG (pfx x).length 1 (fun _ _ y => y) fun i f => decide (i<M x*2*B x ∧ f 0 = (pfx x).getD i false) :=
  ⟨PolyT.length prefix_poly,PolyT.decide_and (PolyT.decide_lt hi (PolyT.comp (PolyT.mul (PolyT.mul hm (PolyT.const 2)) hb) hx)) (PolyT.decide_eq (bit 0) (PolyT.getD (PolyT.comp prefix_poly hx) hi (PolyT.const false)))⟩
theorem decoded_poly : EffG decoded := by
  have hp := prime_poly; have hb := width_poly hp; have hd := PolyT.add hb (PolyT.const 1); have hm := slots_poly hb; have hq := CoreCheck.pad_poly hp
  have hc : PolyT (fun w => min (idx w) 2) := by simp only [min_def]; exact PolyT.ite' (PolyT.decide_le idx_poly (PolyT.const 2)) idx_poly (PolyT.const 2)
  have ho := PolyT.ite' (PolyT.decide_eq idx_poly (PolyT.const 3)) (PolyT.const 1) (PolyT.const 0)
  have hr := rangeP hd hp; have ha := catG_poly hr (catG_poly (orP hd) (catG_poly hr (catG_poly (rangeP hd threshold_poly) (catG_poly hr (hashP hq hd hp)))))
  have hn := PolyT.sub hm (PolyT.const 1); have hch := catG_poly (show EffG (fun _ : W => (0,fun _ _ => false)) from ⟨PolyT.const 0,PolyT.const false⟩) (catG_poly (tileP (PolyT.sub hn (PolyT.const 1)) hr) (tileP hn (stageP hq hd hp)))
  exact catG_poly (anchorsP hc ho hm hd (S8H.PointAddresses.mul_poly.nb hd)) (catG_poly (show EffG (fun _ : W => zeroLastG) from ⟨PolyT.const 1,PolyT.not' (bit 0)⟩) (catG_poly (catG_poly (tileP hm (seedP hd hp)) (preP hm hb)) (catG_poly (tileP hc (tileP hm ha)) (tileP ho (catG_poly hr (tileP hc hch))))))
theorem port_poly : PolyT packetPort := fullPort_poly decoded_poly
theorem local_poly : PolyT (fun z : Row => port z.1 z.2.1 z.2.2) := decoded_poly.2
end DetDLP.S8G.PortPoly


