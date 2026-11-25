-- Prove2me | Definitions.Def_DetDLP_S8H4_PortPoly
-- name    : DetDLP_S8H4_PortPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:28:49.168016+00:00
-- url     : https://prove2.me/theorems/cb810d6d-fe92-41f0-995f-9b1593723b1d
-- title:
--   Tag 4 port evaluator definition and fast PolyT bound
-- statement:
--   For a tag-4 descriptor $w$, the evaluator decodes the field parameters, four seed coordinates, and a prefix, then evaluates a specified port of the resulting gate tree. The theorem `port_poly` proves a uniform polynomial-time bound for this computation on binary words. The selector proof composes conditional choice, bit extraction, and equality for the two coordinates; the prefix proof combines a row bound with a list-bit comparison. Concatenation then gives the bound for the full tree.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H_PortCombinators
import Definitions.Def_DetDLP_S8H4_ElemDecoder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DetDLP.S8H4.PortPoly
open S8H0 S8H.PortCombinators GateSemantics S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes Groundwork LocalGateEq
open ElemDecoder
def tree (q : List Unit) (b p T a0 b0 a1 b1 : ℕ) (c : Coeff) (η : List Bool) :=
  let d := b+1; let w := regR d; let r := catG (rangeG d p) (rangeG d p)
  let base := catG (catG r (manyG 6 fun _ => r)) (catG (manyG 5 fun i => hashG q d p c i.castSucc) (curveG d))
  let mux := rowsG d 3 (fun _ _ x => x) fun i r => decide (r 1 = (if r 0 then a1 else a0).testBit i ∧ r 2 = (if r 0 then b1 else b0).testBit i)
  let pre := rowsG η.length 1 (fun _ _ x => x) fun i r => decide (i < 1+(b+b) ∧ r 0 = η.getD i false)
  catG (anchorsG (regs d+4*d+2)) (catG zeroLastG (catG base (catG (genHashG q d p w w w) (catG mux (catG zeroLastG (catG (rangeG d T) pre))))))
def decoded (w : W) := tree (CoreCheck.pad (prime w)) (width w) (prime w) (threshold w)
  (seedEntry w 0) (seedEntry w 1) (seedEntry w 2) (seedEntry w 3) ⟨coeff w 1,coeff w 2,coeff w 3,coeff w 4,coeff w 5⟩ (pfx w)
def port := fullPort decoded
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.length PolyT.getD PolyT.testBit PolyT.decide_lt PolyT.decide_eq CoreCheck.reorder_poly CoreCheck.column_poly CoreCheck.pad_poly w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly w4_M5Evaluator.clog2_poly RegisterMap.regs_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] S8M.ECPair.Packet.prime_poly S8M.ECPair.Packet.threshold_poly width_poly
attribute [local fun_prop] S8M.ECPair.Packet.prefix_poly
private theorem sixth {Q : W → List Unit} {D P : W → ℕ} (hq : PolyT Q) (hd : PolyT D) (hp : PolyT P) :
    EffG fun x => genHashG (Q x) (D x) (P x) (regR (D x)) (regR (D x)) (regR (D x)) := by
  unfold genHashG prodG; refine catG_poly (catG_poly (catG_poly ?_ ?_) (catG_poly ?_ ?_)) (catG_poly ?_ (catG_poly ?_ ?_))
  all_goals constructor <;> simp only [mulG,eqsG,addG,regR,pinR] <;> fun_prop (disch := assumption)
private abbrev Row := W × ℕ × W
private theorem hx : PolyT (@Prod.fst W (ℕ × W)) := PolyT.fst PolyT.id'
private theorem hi : PolyT (fun z : Row => z.2.1) := PolyT.fst (PolyT.snd PolyT.id')
private theorem bit (k : ℕ) : PolyT (fun z : Row => z.2.2.getD k false) :=
  PolyT.getD (PolyT.snd (PolyT.snd PolyT.id')) (PolyT.const k) (PolyT.const false)
private theorem mux_poly {D A0 B0 A1 B1 : W → ℕ} (hd : PolyT D) (ha0 : PolyT A0) (hb0 : PolyT B0) (ha1 : PolyT A1) (hb1 : PolyT B1) :
    EffG fun x => rowsG (D x) 3 (fun _ _ b => b) fun i r => decide (r 1 = (if r 0 then A1 x else A0 x).testBit i ∧ r 2 = (if r 0 then B1 x else B0 x).testBit i) := by
  have sel {F G : W → ℕ} (hf : PolyT F) (hg : PolyT G) : PolyT (fun z : Row => (if z.2.2.getD 0 false then F z.1 else G z.1).testBit z.2.1) :=
    PolyT.testBit (PolyT.ite' (PolyT.decide_eq (bit 0) (PolyT.const true)) (PolyT.comp hf hx) (PolyT.comp hg hx)) hi
  exact ⟨hd, PolyT.decide_and (PolyT.decide_eq (bit 1) (sel ha1 ha0)) (PolyT.decide_eq (bit 2) (sel hb1 hb0))⟩
private theorem pre_poly {B : W → ℕ} {Y : W → W} (hb : PolyT B) (hy : PolyT Y) :
    EffG fun x => rowsG (Y x).length 1 (fun _ _ b => b) fun i r => decide (i < 1+(B x+B x) ∧ r 0 = (Y x).getD i false) := by
  have bound := PolyT.comp (PolyT.add (PolyT.const 1) (PolyT.add hb hb)) hx
  exact ⟨PolyT.length hy, PolyT.decide_and (PolyT.decide_lt hi bound)
    (PolyT.decide_eq (bit 0) (PolyT.getD (PolyT.comp hy hx) hi (PolyT.const false)))⟩
private theorem range_poly {D P : W → ℕ} (hd : PolyT D) (hp : PolyT P) : EffG fun x => rangeG (D x) (P x) := by
  constructor <;> simp only [rangeG,addG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem base_poly {Q : W → List Unit} {D P : W → ℕ} {C : W → Coeff} (hq : PolyT Q) (hd : PolyT D) (hp : PolyT P)
    (h1 : PolyT fun x => (C x).a1) (h2 : PolyT fun x => (C x).a2) (h3 : PolyT fun x => (C x).a3) (h4 : PolyT fun x => (C x).a4) (h6 : PolyT fun x => (C x).a6) :
    EffG fun x => let r := catG (rangeG (D x) (P x)) (rangeG (D x) (P x)); catG (catG r (manyG 6 fun _ => r)) (catG (manyG 5 fun i => hashG (Q x) (D x) (P x) (C x) i.castSucc) (curveG (D x))) := by
  have hr := catG_poly (range_poly hd hp) (range_poly hd hp)
  refine catG_poly (catG_poly hr (many_poly fun _ => hr)) (catG_poly (many_poly fun i => hash_poly i.castSucc hq hd hp h1 h2 h3 h4 h6) ⟨hd, ?_⟩)
  simp only [curveG,CurveRows.test]; fun_prop (disch := assumption)
private theorem anchors_poly {D : W → ℕ} (hd : PolyT D) : EffG fun x => anchorsG (regs (D x)+4*D x+2) :=
  ⟨PolyT.add (PolyT.add (RegisterMap.regs_poly hd) (PolyT.mul (PolyT.const 4) hd)) (PolyT.const 2), PolyT.const true⟩
private theorem zero_poly : EffG fun _ : W => zeroLastG := by
  exact ⟨PolyT.const 1, PolyT.not' (bit 0)⟩
private theorem tree_poly {Q : W → List Unit} {B P T A0 B0 A1 B1 : W → ℕ} {C : W → Coeff} {Y : W → W}
    (hq : PolyT Q) (hb : PolyT B) (hp : PolyT P) (ht : PolyT T) (ha0 : PolyT A0) (hb0 : PolyT B0) (ha1 : PolyT A1) (hb1 : PolyT B1) (hy : PolyT Y)
    (h1 : PolyT fun x => (C x).a1) (h2 : PolyT fun x => (C x).a2) (h3 : PolyT fun x => (C x).a3) (h4 : PolyT fun x => (C x).a4) (h6 : PolyT fun x => (C x).a6) :
    EffG fun x => tree (Q x) (B x) (P x) (T x) (A0 x) (B0 x) (A1 x) (B1 x) (C x) (Y x) := by
  have hd : PolyT fun x => B x + 1 := PolyT.add hb (PolyT.const 1)
  exact catG_poly (anchors_poly hd) (catG_poly zero_poly (catG_poly (base_poly hq hd hp h1 h2 h3 h4 h6)
    (catG_poly (sixth hq hd hp) (catG_poly (mux_poly hd ha0 hb0 ha1 hb1)
    (catG_poly zero_poly (catG_poly (range_poly hd ht) (pre_poly hb hy)))))))
/-- A single polynomial-time machine handles every tag-4 descriptor. -/
theorem port_poly : Groundwork.PolyT port := by
  have hk (k : ℕ) : PolyT fun w : W => (w,k) := PolyT.prodMk PolyT.id' (PolyT.const k)
  have hc (k : ℕ) := PolyT.comp coeff_poly (hk k)
  have hs (k : ℕ) := PolyT.comp seedEntry_poly (hk k)
  apply fullPort_poly; unfold decoded
  exact tree_poly (C:=fun w => ⟨ElemDecoder.coeff w 1,ElemDecoder.coeff w 2,ElemDecoder.coeff w 3,ElemDecoder.coeff w 4,ElemDecoder.coeff w 5⟩) (CoreCheck.pad_poly S8M.ECPair.Packet.prime_poly) width_poly S8M.ECPair.Packet.prime_poly S8M.ECPair.Packet.threshold_poly (hs 0) (hs 1) (hs 2) (hs 3) S8M.ECPair.Packet.prefix_poly (hc 1) (hc 2) (hc 3) (hc 4) (hc 5)
end DetDLP.S8H4.PortPoly


