-- Prove2me | Definitions.Def_DetDLP_S8N_PortPoly
-- name    : DetDLP_S8N_PortPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:10:12.903648+00:00
-- url     : https://prove2.me/theorems/2f72c40f-a207-5313-b3bb-2917b2f786e9
-- title:
--   Tag 2 uniform PolyT port evaluator bound
-- statement:
--   For every Tag 2 input word w, the decoded circuit family has a polynomial-time uniform evaluator: the gate count and local gate predicate are computable in time polynomial in the encoded input length. The port function is the full port packet induced by the decoded gate circuit, using the circuit predicate on in-range gate indices and the agreement predicate outside the gate range. Therefore the port evaluator satisfies PolyT(port). The proof establishes EffG(decoded) by composing polynomial evaluators for the anchor prefix, zero-last row, repeated elliptic-curve seed slots and prefix bits, fixed atoms, map stages, target range checks, and folded addition chain. Each repeated block is indexed with the quotient/remainder tabulation evaluator, while hash predicates are handled through explicit polynomial operands and the pre-proved polynomial conditional evaluator.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8N_PortDefs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.PortPoly
open Groundwork S8H0 S8H.PortCombinators RegisterMap DetDLP_W1_Queries
open DetDLP.S8M.PortPoly (bit tab tile rd atomFixed mapG addStepG prime coeff bTwo cTerm width slots prefixG)
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.length PolyT.getD PolyT.testBit PolyT.decide_lt PolyT.decide_eq PolyT.div PolyT.mod CoreCheck.reorder_poly CoreCheck.column_poly CoreCheck.pad_poly w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly w4_M5Evaluator.clog2_poly S8G.FpMoment.Code.width_poly S8G.FpMoment.Code.slots_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 PolyT.drop PolyT.take PolyT.reverse w5_M6Sort.decode_poly first_poly more_poly
variable {α β : Type} [Enc α] [Enc β]
@[local fun_prop] theorem prime_poly : PolyT prime := by unfold DetDLP.S8M.PortPoly.prime DetDLP_W1_Queries.second; fun_prop
@[local fun_prop] theorem threshold_poly : PolyT threshold := by unfold threshold third DetDLP_W1_Queries.second; fun_prop
@[local fun_prop] theorem prefix_poly : PolyT prefixBits := by unfold prefixBits third DetDLP_W1_Queries.second; fun_prop
@[local fun_prop] theorem idx_poly : PolyT idx := by unfold idx third DetDLP_W1_Queries.second; fun_prop
theorem pull {F : β → GC} {u : α → β} (hf : EffG F) (hu : PolyT u) : EffG fun x => F (u x) := by
  have h := PolyT.comp hf.1 hu
  have k := PolyT.comp hf.2 (PolyT.prodMk (PolyT.comp hu (PolyT.fst (PolyT.id' (α:=α × ℕ × W)))) (PolyT.snd PolyT.id'))
  exact ⟨h,k⟩
theorem tabP {n : α → ℕ} {F : α → ℕ → GC} (hn : PolyT n) (h : EffG fun z : α × ℕ => F z.1 z.2) : EffG fun x => tab (n x) (F x) := by
  have hk := PolyT.comp h.1 (PolyT.prodMk PolyT.id' (PolyT.const 0))
  have k := PolyT.comp hk (PolyT.fst (PolyT.id' (α:=α × ℕ × W)))
  have i := PolyT.fst (PolyT.snd (PolyT.id' (α:=α × ℕ × W)))
  exact ⟨PolyT.mul hn hk,PolyT.comp h.2 (PolyT.prodMk (PolyT.prodMk (PolyT.fst PolyT.id') (PolyT.div i k)) (PolyT.prodMk (PolyT.mod i k) (PolyT.snd (PolyT.snd PolyT.id'))))⟩
theorem tileP {n : α → ℕ} {F : α → GC} (hn : PolyT n) (h : EffG F) : EffG fun x => tile (n x) (F x) := tabP hn (pull h (PolyT.fst PolyT.id'))
variable {q : α → List Unit} {d p a x b : α → ℕ}
theorem hashP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (ha : PolyT a) (hx : PolyT x) (hb : PolyT b) : EffG fun z => DetDLP.S8M.PortPoly.hash (q z) (d z) (p z) (a z) (x z) (b z) := by
  unfold DetDLP.S8M.PortPoly.hash genHashG prodG
  refine catG_poly (catG_poly (catG_poly ?_ ?_) (catG_poly ?_ ?_)) (catG_poly ?_ (catG_poly ?_ ?_))
  all_goals constructor <;> simp only [mulG,eqsG,addG,rd,ite_apply,regR,pinR] <;> fun_prop (disch := assumption)
theorem rangeP (hd : PolyT d) (hp : PolyT p) : EffG fun z => rangeG (d z) (p z) := by
  constructor <;> simp only [rangeG,addG,regR,pinR] <;> fun_prop (disch := assumption)
theorem fixedP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) {t : α → ℕ} (ht : PolyT t) {c : α → GateRoutes.Coeff} (h1 : PolyT fun z => (c z).a1) (h2 : PolyT fun z => (c z).a2) (h3 : PolyT fun z => (c z).a3) (h4 : PolyT fun z => (c z).a4) (h6 : PolyT fun z => (c z).a6) : EffG fun z => atomFixed (q z) (d z) (p z) (t z) (c z) := by
  refine catG_poly (catG_poly (tileP (PolyT.const 16) (rangeP hd hp)) (catG_poly (many_poly fun i => hash_poly i.castSucc hq hd hp h1 h2 h3 h4 h6) ?_)) (catG_poly (hashP hq hd hp (PolyT.const 0) (PolyT.const 0) (PolyT.const 0)) (catG_poly ?_ (rangeP hd ht)))
  all_goals constructor <;> simp only [curveG,CurveRows.test,zeroLastG] <;> fun_prop (disch := assumption)
theorem mapP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (hb : PolyT b) (ha : PolyT a) (hx : PolyT x) : EffG fun z => mapG (q z) (d z) (p z) (b z) (a z) (x z) := by
  refine catG_poly (tileP (PolyT.const 10) (rangeP hd hp)) (catG_poly (catG_poly ?_ (catG_poly ?_ (catG_poly ?_ ?_))) (catG_poly ?_ (tileP (PolyT.const 2) ?_)))
  iterate 4 (refine hashP hq hd hp ?_ ?_ ?_ <;> fun_prop (disch := assumption))
  all_goals constructor <;> dsimp only [bit] <;> fun_prop (disch := assumption)
theorem stepP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (ha : PolyT a) : EffG fun z => addStepG (q z) (d z) (p z) (a z) := by
  have hw := PolyT.snd (PolyT.snd (PolyT.id' (α:=α × ℕ × W)))
  have hb (k : ℕ) : PolyT fun z : α × ℕ × W => bit z.2.2 k := PolyT.getD hw (PolyT.const k) (PolyT.const false)
  have hi := PolyT.fst (PolyT.snd (PolyT.id' (α:=α × ℕ × W)))
  have asC {c : α × ℕ × W → Bool} (hc : PolyT c) : PolyT fun x => decide (c x = true) := PolyT.decide_eq hc (PolyT.const true)
  refine catG_poly (tileP (PolyT.const 34) (rangeP hd hp)) (catG_poly (many_poly fun i => ?_) (catG_poly (tileP (PolyT.const 2) ?_) (catG_poly ?_ (catG_poly ?_ (tileP (PolyT.const 2) ?_)))))
  · apply hashP hq hd hp <;> fin_cases i <;> dsimp only [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go,Fin.ofNat,Fin.succ] <;> fun_prop (disch := assumption)
  · exact ⟨hd, P2M_Groundwork_PolyT_ite__226169acf219 (asC (hb 0)) (PolyT.and' (PolyT.not' (hb 1)) (PolyT.not' (hb 2))) (PolyT.beq' (hb 3) (PolyT.testBit (PolyT.const 1) hi))⟩
  · exact ⟨hd, PolyT.beq' (hb 6) (P2M_Groundwork_PolyT_ite__226169acf219 (asC (PolyT.and' (PolyT.and' (PolyT.not' (hb 0)) (PolyT.not' (hb 1))) (PolyT.not' (hb 2)))) (hb 4) (P2M_Groundwork_PolyT_ite__226169acf219 (asC (PolyT.and' (PolyT.and' (PolyT.and' (PolyT.not' (hb 0)) (PolyT.not' (hb 1))) (hb 2)) (PolyT.not' (hb 3)))) (hb 5) (PolyT.const false)))⟩
  · exact ⟨PolyT.const 1, PolyT.beq' (hb 4) (P2M_Groundwork_PolyT_ite__226169acf219 (asC (hb 0)) (hb 1) (PolyT.and' (PolyT.and' (PolyT.not' (hb 1)) (hb 2)) (hb 3)))⟩
  · exact ⟨hd, PolyT.beq' (hb 7) (P2M_Groundwork_PolyT_ite__226169acf219 (asC (hb 0)) (hb 5) (P2M_Groundwork_PolyT_ite__226169acf219 (asC (hb 1)) (hb 4) (P2M_Groundwork_PolyT_ite__226169acf219 (asC (PolyT.and' (hb 2) (hb 3))) (PolyT.const false) (hb 6))))⟩
theorem seedP (hd : PolyT d) (hp : PolyT p) : EffG fun z => seedSlotG (d z) (p z) := by
  refine catG_poly (rangeP hd (PolyT.sub hp (PolyT.const 1))) (catG_poly (rangeP hd hp) ?_)
  constructor <;> simp only [addG,regR,pinR] <;> fun_prop (disch := assumption)
theorem prefixP {n : α → ℕ} {e : α → W} (hn : PolyT n) (he : PolyT e) : EffG fun z => prefixG (n z) (e z) := by
  constructor <;> dsimp only [prefixG,bit] <;> fun_prop (disch := assumption)
theorem foldChainP {n : α → ℕ} (hn : PolyT n) (hd : PolyT d) (hg : EffG fun z : α => addStepG (q z) (d z) (p z) (a z)) : EffG fun z => foldChainG (n z) (d z) (addStepG (q z) (d z) (p z) (a z)) := by
  refine catG_poly ?_ (catG_poly ?_ (catG_poly ?_ (tileP hn hg)))
  all_goals constructor <;> dsimp only [foldChainG,bit] <;> fun_prop (disch := assumption)
theorem atomSlotP (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) {t : α → ℕ} (ht : PolyT t) {c : α → GateRoutes.Coeff} (h1 : PolyT fun z => (c z).a1) (h2 : PolyT fun z => (c z).a2) (h3 : PolyT fun z => (c z).a3) (h4 : PolyT fun z => (c z).a4) (h6 : PolyT fun z => (c z).a6) : EffG fun z => atomSlotG (q z) (d z) (p z) (t z) (c z) := by
  have h := fixedP hq hd hp ht h1 h2 h3 h4 h6
  refine catG_poly h ?_
  constructor <;> dsimp only [bit] <;> fun_prop (disch := assumption)
theorem targetP (hd : PolyT d) (hp : PolyT p) : EffG fun z => targetG (d z) (p z) := by
  refine catG_poly (rangeP hd hp) (catG_poly (rangeP hd hp) ?_)
  constructor <;> dsimp only [bit] <;> fun_prop (disch := assumption)
theorem decoded_poly : EffG decoded := by
  have hp := prime_poly
  have hb := S8G.FpMoment.Code.width_poly hp
  have hd := PolyT.add hb (PolyT.const 1)
  have hm := S8G.FpMoment.Code.slots_poly hb
  have hq := CoreCheck.pad_poly hp
  have hc (k : ℕ) : PolyT (fun w : List Bool => (w5_M6Sort.decode (second w)).getD k 0) := by unfold second; fun_prop
  have hfixed := fixedP (c:=coeff) hq hd hp threshold_poly (hc 1) (hc 2) (hc 3) (hc 4) (hc 5)
  have h2 : PolyT bTwo := by unfold bTwo; dsimp only [coeff,second]; fun_prop
  have ht : PolyT cTerm := by unfold cTerm; dsimp only [coeff,second]; fun_prop (disch := assumption)
  have hj : PolyT (fun w : List Bool => min (idx w) 2) := by simp only [min_def]; exact PolyT.ite' (PolyT.decide_le idx_poly (PolyT.const 2)) idx_poly (PolyT.const 2)
  have ho : PolyT (fun w : List Bool => if idx w = 3 then 1 else 0) := PolyT.ite' (PolyT.decide_eq idx_poly (PolyT.const 3)) (PolyT.const 1) (PolyT.const 0)
  have hseed : EffG (fun w : List Bool => ecSeedG (slots (width (prime w))) (width (prime w)) (width (prime w)+1) (prime w) (prefixBits w)) := by
    have hs := tileP hm (catG_poly (seedP hd hp) (seedP hd hp))
    have he := prefixP (PolyT.mul (PolyT.mul hm (PolyT.const 4)) hb) prefix_poly
    exact catG_poly hs he
  have hatom : EffG (fun w : List Bool => atomSlotG (CoreCheck.pad (prime w)) (width (prime w)+1) (prime w) (threshold w) (coeff w)) := atomSlotP hq hd hp threshold_poly (hc 1) (hc 2) (hc 3) (hc 4) (hc 5)
  have hatoms := tileP hj (tileP hm hatom)
  have hmap := tileP (PolyT.mul (PolyT.const 2) hm) (mapP hq hd hp h2 (hc 1) (hc 3))
  have hfold := foldChainP (PolyT.sub hm (PolyT.const 1)) hd (stepP hq hd hp ht)
  have hprod := catG_poly (targetP hd hp) (catG_poly hmap (tileP (PolyT.const 2) hfold))
  let an := fun w : List Bool => anchorCount (min (idx w) 2) (if idx w = 3 then 1 else 0) (slots (width (prime w))) (width (prime w)+1) (S8H.PointAddresses.wires (width (prime w)+1))
  have han : PolyT an := by
    dsimp [an,anchorCount]
    have hmin := hj
    have hw := hb
    have hslots := hm
    have hwire := S8H.PointAddresses.mul_poly.nb hd
    fun_prop (disch := assumption)
  have hanchor : EffG (fun w : List Bool => anchorsG (an w)) := ⟨han,PolyT.const true⟩
  have hzero : EffG (fun _ : List Bool => zeroLastG) := ⟨PolyT.const 1,PolyT.not' (PolyT.getD (PolyT.snd (PolyT.snd (PolyT.id' (α:=List Bool × ℕ × List Bool)))) (PolyT.const 0) (PolyT.const false))⟩
  exact catG_poly hanchor (catG_poly hzero (catG_poly hseed (catG_poly hatoms (tileP ho hprod))))
theorem port_poly : PolyT port := fullPort_poly decoded_poly
end DetDLP.S8N.PortPoly


