-- Prove2me | Definitions.Def_DetDLP_S8H_PortCombinators
-- name    : DetDLP_S8H_PortCombinators
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:06:16.848482+00:00
-- url     : https://prove2.me/theorems/4c78712a-4efa-4424-ab69-63b789aa11ac
-- title:
--   Public reusable GC port-evaluator combinators for register networks
-- statement:
--   **Gate evaluators.** A gate evaluator is a pair $(N,e)$, where $N$ is the gate count and $e(i,a)$ checks gate $i$ on the local input bits $a$. Concatenation adds the gate counts and subtracts the first count when dispatching to the second evaluator. `many_spec` and `many_poly` extend correctness and polynomial-time evaluation to a fixed finite sequence of blocks.
--
--   **Port evaluation.** Suppose `FitsG (F w) B` holds. For every wiring of $B$, every subdivision vertex $v$, and every port assignment $a$, `fullPort_eval` identifies the encoded answer on $(w,v,a)$ with the subdivision tensor at $(v,a)$. Gate vertices use the local checker; all other vertices use bit agreement. `fullPort_poly` proves polynomial-time evaluation when the gate count and indexed checker satisfy `EffG F`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_GateDispatchEq
import Definitions.Def_DetDLP_S8H0_LocalGateEq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DetDLP.S8H.PortCombinators
open DetDLP.S8H0 Groundwork DetDLP.S8H0.GateAgree DetDLP.S8H0.LocalGateEq DetDLP.S8H0.GateRoutes DetDLP.S8H0.RegisterMap DetDLP.S8H0.NamedBlocks S8J S8J.CircuitRealizes
abbrev GC := ℕ × (ℕ → List Bool → Bool)
def catG (a b : GC) : GC := (a.1+b.1, fun i w => if i<a.1 then a.2 i w else b.2 (i-a.1) w)
def FitsG (c : GC) (B : Block) := c.1 = B.A.ng ∧ ∀ (i : Fin B.A.ng) (w : List Bool), c.2 i w = localCheck B.A B.t i w
theorem catG_spec {a b : GC} {A B : Block} (ha : FitsG a A) (hb : FitsG b B) : FitsG (catG a b) ⟨join A.A B.A,joinTest A.t B.t⟩ := by
  refine ⟨congrArg₂ (·+·) ha.1 hb.1,fun i w => ?_⟩; induction i using Fin.addCases with
  | left i => simp only [catG,ha.1,Fin.val_castAdd,if_pos i.isLt,ha.2,join_left]
  | right i => simp only [catG,ha.1,Fin.val_natAdd,Nat.not_lt_of_le (Nat.le_add_right ..),if_false,Nat.add_sub_cancel_left,hb.2,join_right]
theorem catB {k : ℕ} {a b : GC} {A B : B k} (ha : FitsG a A.core) (hb : FitsG b B.core) : FitsG (catG a b) (joinB A B).core := catG_spec ha hb
def manyG : (n : ℕ) → (Fin (n+1) → GC) → GC
  | 0,f => f 0
  | n+1,f => catG (f 0) (manyG n fun i => f i.succ)
theorem many_spec {k n : ℕ} {f : Fin (n+1) → GC} {b : Fin (n+1) → B k} (h : ∀ i, FitsG (f i) (b i).core) : FitsG (manyG n f) (RangeRows.many n b).core := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact catB (h 0) (ih fun i => h i.succ)

abbrev Reader := ℕ → Bool → Bool
def regR (n : ℕ) : Reader := fun i b => if i<n then b else false
def pinR (k : ℕ) : Reader := fun i _ => k.testBit i
def anchorsG (n : ℕ) : GC := (n,fun _ _ => true)
def zeroLastG : GC := (1,fun _ w => !w.getD 0 false)
def curveG (n : ℕ) : GC := (n,fun _ w => CurveRows.test (w.getD 0 false) (w.getD 1 false) (w.getD 2 false) (w.getD 3 false) (w.getD 4 false))
def addG (n : ℕ) (v : Bool) (a b z : Reader) : GC := (n,fun i w => CoreCheck.column n i (a i (w.getD 0 false)) (b i (w.getD 1 false)) (z i (w.getD 2 false)) (if i=0 then v else w.getD 4 false) (w.getD 3 false))
def mulG (q : List Unit) (d : ℕ) : GC := (w4_M5GraphBounds.vertexCount d,fun i w => w4_M5Dispatch.evalNat q i (CoreCheck.reorder q i w))
def eqsG (d : ℕ) (a b z : Reader) : GC := (4*d,fun i w => decide (w.getD 0 false = (if i<d then a i (w.getD 1 false) else if i<2*d then b (i-d) (w.getD 1 false) else z (i-2*d) (w.getD 1 false))))
def prodG (q : List Unit) (d : ℕ) (a b z : Reader) := catG (mulG q d) (eqsG d a b z)
def operandsG (d : ℕ) (c : Coeff) (s : Fin 7) : Reader × Reader × Reader :=
  let w := regR d
  if s.val=0 then (pinR c.a1,w,w) else if s.val=1 then (pinR 1,w,pinR c.a3) else
  if s.val=2 then (w,w,pinR 0) else if s.val=3 then (pinR 1,w,pinR c.a2) else
  if s.val=4 then (w,w,pinR c.a4) else if s.val=5 then (w,w,pinR c.a6) else (pinR 0,w,pinR 0)
def hashG (q : List Unit) (d p : ℕ) (c : Coeff) (s : Fin 7) :=
  let v := operandsG d c s; let w := regR d; let z := regR (2*d); let u := regR (d+1)
  catG (catG (prodG q d v.1 v.2.1 z) (prodG q d w (pinR p) z))
    (catG (addG (2*d) false z w z) (catG (addG (d+1) false w v.2.2 u) (addG (d+1) false w (fun i x => p.testBit i && x) u)))
def rangeG (d p : ℕ) := addG (d+1) true (regR d) (regR d) (pinR p)
def body (q : List Unit) (d p : ℕ) (c : Coeff) :=
  let r := catG (rangeG d p) (rangeG d p)
  catG (anchorsG (regs d+1)) (catG zeroLastG (catG (catG r (manyG 6 fun _ => r)) (catG (manyG 6 (hashG q d p c)) (curveG d))))
def orderGC (p : ℕ) (c : Coeff) := body (CoreCheck.pad p) (GateSemantics.d p) p c

theorem add_spec {s : Shape} {n : ℕ} (v : Bool) {a b z : Reader} {A B Z C : Fin n → Ref s} (ha : ∀ (i : Fin n) x, a i x = (A i).read x) (hb : ∀ (i : Fin n) x, b i x = (B i).read x) (hz : ∀ (i : Fin n) x, z i x = (Z i).read x) (hc : ∀ (i : Fin n) x, (C i).read x = x) : FitsG (addG n v a b z) (NamedBlocks.add v A B Z C).core := ⟨rfl, fun i w => by rw [add_local]; simp only [addG,ha,hb,hz,hc]⟩
theorem prod_spec {s : Shape} {d : ℕ} (h : 1 ≤ d) {a b z : Reader} {A B Z : HashRows.Word s} {C : Fin (w3_fpMulLayout d h).nb → Addr s} (ha : ∀ i x, a i x = (A i).read x) (hb : ∀ i x, b i x = (B i).read x) (hz : ∀ i x, z i x = (Z i).read x) : FitsG (prodG (List.replicate d ()) d a b z) (HashRows.product h A B Z (fun i => .reg (C i))).core := by
  apply catB
  · refine ⟨rfl,fun i w => ?_⟩; change w4_M5Dispatch.evalNat _ _ _ = _
    generalize hq : List.replicate d () = q; have hl : q.length=d := by simp [←hq]
    subst d; exact (mul_register_local q h C i w).symm
  · refine ⟨rfl,fun i w => ?_⟩; rw [eqs_local]; simp only [eqsG,HashRows.busRef,Ref.read]; split_ifs <;> simp [ha,hb,hz,Ref.read]
theorem range_spec {d : ℕ} {s : Shape} (p : ℕ) (a : Addr (triple d) → Addr s) : FitsG (rangeG d p) (RangeRows.checker p a).core := by
  apply add_spec <;> intros <;> simp only [RangeRows.pad,regR,pinR,Ref.read] <;> split_ifs <;> rfl
theorem hash_spec {d : ℕ} (h : 1 ≤ d) (p : ℕ) (c : Coeff) (s : Fin 7) : FitsG (hashG (List.replicate d ()) d p c s) (HashRows.block p (wires h p c s)).core := by
  unfold hashG HashRows.block
  refine catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))
  all_goals first | apply prod_spec | apply add_spec
  all_goals intros; simp only [wires,GateRoutes.rword,GateRoutes.quot,GateRoutes.word,HashRows.padded,HashRows.pub,regR,pinR,Ref.read]; try (split_ifs <;> rfl)
  all_goals rename_i i x; fin_cases s <;> by_cases hi : (i : ℕ)<d <;> simp [operandsG,operands,Fin.isValue,GateRoutes.rword,GateRoutes.word,HashRows.padded,HashRows.pub,regR,pinR,Ref.read,hi]
theorem pad_eq (p : ℕ) : CoreCheck.pad p = List.replicate (GateSemantics.d p) () := by
  have h : (CoreCheck.pad p).length=GateSemantics.d p := by simp [CoreCheck.pad,GateSemantics.d,S8H.ECPointArithmetic.width,←S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.width]
  rw [←h]; exact List.eq_replicate_of_mem (by simp)
theorem orderGC_spec (p : ℕ) (c : Coeff) : FitsG (orderGC p c) (PointGraph.C p c) := by
  unfold orderGC body; rw [pad_eq,←GraphBudget.anchorSize p]
  refine catG_spec (A:=⟨AnchoredLayout.anchors _,fun _ _ => true⟩) (B:=(PointGraph.net p c).core) ⟨rfl,fun _ _ => rfl⟩ ?_
  unfold PointGraph.net network RangeRows.block
  refine catB ⟨rfl,fun g w => (zeroLast_local _ g w).symm⟩ (catB (catB (catB (range_spec ..) (range_spec ..)) (many_spec fun i => catB (range_spec ..) (range_spec ..))) (catB (many_spec fun i => hash_spec _ _ _ i) ?_))
  refine ⟨rfl,fun i w => ?_⟩; unfold CurveRows.block; rw [rows_local]; rfl

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.length PolyT.getD PolyT.testBit PolyT.decide_lt PolyT.decide_eq CoreCheck.reorder_poly CoreCheck.column_poly CoreCheck.pad_poly w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly w4_M5Evaluator.clog2_poly RegisterMap.regs_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
variable {α : Type} [Enc α]
def EffG (F : α → GC) := (PolyT fun x => (F x).1) ∧ (PolyT fun z : α × ℕ × List Bool => (F z.1).2 z.2.1 z.2.2)
theorem catG_poly {F H : α → GC} (f : EffG F) (h : EffG H) : EffG fun x => catG (F x) (H x) := by
  let π := @Prod.fst α (ℕ × List Bool)
  have hp : PolyT π := PolyT.fst PolyT.id'
  have hc := PolyT.comp f.1 hp
  have hi : PolyT fun z : α × ℕ × List Bool => z.2.1 := by fun_prop
  have hw : PolyT fun z : α × ℕ × List Bool => z.2.2 := by fun_prop
  exact ⟨PolyT.add f.1 h.1,P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hi hc) f.2 (PolyT.comp h.2 (PolyT.prodMk hp (PolyT.prodMk (PolyT.sub hi hc) hw)))⟩
theorem many_poly {n : ℕ} {F : Fin (n+1) → α → GC} (h : ∀ i, EffG (F i)) : EffG fun x => manyG n (fun i => F i x) := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact catG_poly (h 0) (ih fun i => h i.succ)
theorem hash_poly {q : α → List Unit} {D P : α → ℕ} {C : α → Coeff} (s : Fin 7) (hq : PolyT q) (hd : PolyT D) (hp : PolyT P)
    (h1 : PolyT fun x => (C x).a1) (h2 : PolyT fun x => (C x).a2) (h3 : PolyT fun x => (C x).a3) (h4 : PolyT fun x => (C x).a4) (h6 : PolyT fun x => (C x).a6) : EffG fun x => hashG (q x) (D x) (P x) (C x) s := by
  have fstP : PolyT (@Prod.fst α (ℕ × List Bool)) := PolyT.fst PolyT.id'
  have h1' := PolyT.comp h1 fstP; have h2' := PolyT.comp h2 fstP; have h3' := PolyT.comp h3 fstP
  have h4' := PolyT.comp h4 fstP; have h6' := PolyT.comp h6 fstP
  unfold hashG prodG
  refine catG_poly (catG_poly (catG_poly ?_ ?_) (catG_poly ?_ ?_)) (catG_poly ?_ (catG_poly ?_ ?_))
  all_goals constructor <;> simp only [mulG,eqsG,addG,regR,pinR] <;> try fun_prop (disch := assumption)
  all_goals fin_cases s <;> simp (disch := decide) only [operandsG,if_pos,if_neg,regR,pinR] <;> fun_prop (disch := assumption)
theorem body_poly {q : α → List Unit} {D P : α → ℕ} {C : α → Coeff} (hq : PolyT q) (hd : PolyT D) (hp : PolyT P)
    (h1 : PolyT fun x => (C x).a1) (h2 : PolyT fun x => (C x).a2) (h3 : PolyT fun x => (C x).a3) (h4 : PolyT fun x => (C x).a4) (h6 : PolyT fun x => (C x).a6) : EffG fun x => body (q x) (D x) (P x) (C x) := by
  have hr : EffG fun x => rangeG (D x) (P x) := by constructor <;> simp only [rangeG,addG,regR,pinR] <;> fun_prop (disch := assumption)
  unfold body
  refine catG_poly ?_ (catG_poly ?_ (catG_poly (catG_poly (catG_poly hr hr) (many_poly fun _ => catG_poly hr hr)) (catG_poly (many_poly fun i => hash_poly i hq hd hp h1 h2 h3 h4 h6) ?_)))
  all_goals constructor <;> simp only [anchorsG,zeroLastG,curveG,CurveRows.test] <;> fun_prop (disch := assumption)

/-- Concatenate rows indexed from zero through the supplied bound. -/
def manyN_G (n : ℕ) (f : ℕ → GC) : GC := manyG n fun i => f i.val

def rowsG (n m : ℕ) (r : ℕ → Fin m → Bool → Bool) (t : ℕ → (Fin m → Bool) → Bool) : GC :=
  (n, fun i w => t i fun j => r i j (w.getD j.val false))

def genHashG (q : List Unit) (d p : ℕ) (a b c : Reader) : GC :=
  let w := regR d; let z := regR (2*d); let u := regR (d+1)
  catG (catG (prodG q d a b z) (prodG q d w (pinR p) z))
    (catG (addG (2*d) false z w z) (catG (addG (d+1) false w c u)
      (addG (d+1) false w (fun i x => p.testBit i && x) u)))

abbrev fullPort (F : List Bool → GC) := S8C.portPacket (fun z =>
  if z.2.1 < (F z.1).1 then (F z.1).2 z.2.1 z.2.2 else PortEval.agree z.2.2)

theorem fullPort_poly {F : List Bool → GC} (h : EffG F) : PolyT (fullPort F) := by
  have hf : PolyT (@Prod.fst (List Bool) (ℕ × List Bool)) := PolyT.fst PolyT.id'
  have hc := PolyT.comp h.1 hf
  apply S8C.portPacket_poly
  exact P2M_Groundwork_PolyT_ite__226169acf219
    (PolyT.decide_lt (PolyT.fst (PolyT.snd PolyT.id')) hc)
    h.2 (PolyT.comp PortEval.agree_poly (PolyT.snd (PolyT.snd PolyT.id')))

private theorem nonGate {k : ℕ} (B : Block) (W : Wiring B.A.ne k)
    (v : Fin (G B W).subdivision.nV) (a) (hv : ¬ v.val < B.A.ng) :
    PortEval.agree (List.ofFn a) = (G B W).subdivisionTensor (CircuitRealizes.T B W) v a := by
  induction v using Fin.addCases with
  | right e => exact PortEval.edge_eq _ _ e a
  | left v => induction v using Fin.addCases with
    | left g => induction g using Fin.addCases with
      | left g => exact False.elim (hv g.isLt)
      | right b => exact PortEval.cycle_eq B.A.gate W.next B.t b a
    | right b => exact PortEval.bit_eq _ _ b a

open w4_M5Network in
theorem fullPort_eval {F : List Bool → GC} {w : List Bool} {k : ℕ} (B : Block)
    (W : Wiring B.A.ne k) (h : FitsG (F w) B) (v : Fin (G B W).subdivision.nV) (a) :
    fullPort F (encodePortQuery w v.val (List.ofFn a)) = encodeNatListBin
      [if (G B W).subdivisionTensor (CircuitRealizes.T B W) v a then 1 else 0] := by
  unfold fullPort; rw [S8C.portPacket_eq]; dsimp only; rw [h.1]; split
  · rename_i hv; let g : Fin B.A.ng := ⟨v.val,hv⟩
    have H : (F w).2 v.val (List.ofFn a) = (G B W).subdivisionTensor (CircuitRealizes.T B W) v a :=
      (h.2 g _).trans (core_tensor B W g a)
    rw [H]
  · rw [nonGate B W v a (by assumption)]
end DetDLP.S8H.PortCombinators


