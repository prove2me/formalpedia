-- Prove2me | Definitions.Def_DetDLP_S8L_PortEval
-- name    : DetDLP_S8L_PortEval
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:08:14.182445+00:00
-- url     : https://prove2.me/theorems/31cb8e26-516a-4e66-b6ae-010b5f274f0f
-- title:
--   Tag 5 uniform PolyT port tensor evaluator
-- statement:
--   ## Tag 5 port evaluator\n\nDefine a single uniform polynomial-time Boolean evaluator for Tag 5 port queries. The evaluator composes gate-local combinators for the atom checks, modular multiplication and range checks, chain stages, prefix constraints, and anchored-layout sentinels.\n\nFor a port query at subdivision vertex \(v\) with incident bits \(a\), the result is the singleton natural-list encoding of the local subdivision tensor \(T(v,a)\) of the factor-graph instance induced by the packet parameters. The proof establishes uniform polynomial-time behavior and exact evaluation for every prime modulus, seed, target unit, threshold, prefix, vertex, and local bit assignment.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_Bounds
import Definitions.Def_DetDLP_S8L_FpPairPacket
import Definitions.Def_DetDLP_S8H0_GateDispatchEq
import Definitions.Def_DetDLP_S8C3_PortEval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
set_option linter.unusedSimpArgs false
namespace DetDLP.S8L.PortEval
open Groundwork S8H0 GateDispatchEq GateAgree LocalGateEq RegisterMap NamedBlocks S8J CircuitRealizes S8C M89S1 S8G.FpAtomRows DetDLP_W1_Queries
open private addG add_spec prodG prod_spec rangeG range_spec regR pinR pad_eq catB mulG eqsG from Definitions.Def_DetDLP_S8H0_GateDispatchEq
open S8H.PointAddresses (wires wires_eq mul_poly)
open private nonGate from Definitions.Def_DetDLP_S8C3_PortEval
private abbrev W := List Bool
/-- Random access to a family of equal-length blocks; the empty family has no gates. -/
private def manyG (n : ℕ) (f : ℕ → GC) : GC := let c := (f 0).1; (n*c,fun i => (f (i/c)).2 (i%c))
private theorem manyFits {k n c : ℕ} (hc : 0<c) (f : ℕ → GC) (b : Fin n → B (k+1)) (sz : ∀ j, (f j).1=c) (h : ∀ i : Fin n, FitsG (f i) (b i).core) : FitsG (manyG n f) (Routes.allRows n b).core := by
  induction n generalizing f with
  | zero => exact ⟨Nat.zero_mul _,fun i => Fin.elim0 i⟩
  | succ n ih =>
    have H := catB (h 0) (ih (fun j => f (j+1)) (fun i => b i.succ) (fun j => sz _) (fun i => h i.succ))
    rw [Routes.allRows]; refine ⟨?_,fun i w => ?_⟩
    · simpa only [manyG,catG,sz,Nat.succ_mul,Nat.add_comm] using H.1
    · rw [←H.2 i w]; simp only [manyG,catG,sz]; split_ifs with hi
      · simp [Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
      · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi); rw [hj]; simp [Nat.add_div_left _ hc]

/-- A single atom checks its hash, register ranges, nonzero input, and threshold. -/
private def atomG (q : List Unit) (d p T a b : ℕ) :=
  let r := regR d; let z := regR (2*d); let u := regR (d+1)
  let h := catG (catG (prodG q d (pinR a) r z) (prodG q d r (pinR p) z)) (catG (addG (2*d) false z r z) (catG (addG (d+1) false r (pinR b) u) (addG (d+1) false r (fun i x => p.testBit i && x) u)))
  let R := rangeG d p
  catG h (catG R (catG (addG d true r (fun _ _ => false) r) (catG R (catG R (catG (rangeG d (min T p)) (d,fun _ w => decide (w.getD 0 false = w.getD 1 false)))))))
private def stageG (q : List Unit) (d p m X j : ℕ) := let r := regR d; let z := regR (2*d)
  catG (catG (prodG q d r r z) (prodG q d r (pinR p) z)) (addG (2*d) false z (fun i x => if j<2*m-2 then r i x else X.testBit i) z)
private theorem atomFits {m d : ℕ} (hd : 1≤d) (p T : ℕ) (cs : Fin m → ℕ × ℕ) (i : Fin (2*m)) : let j : Fin m := ⟨i%m,Nat.mod_lt _ (by have := i.isLt; omega)⟩; FitsG (atomG (List.replicate d ()) d p T (cs j).1 (cs j).2) (Routes.atomRows hd p T cs i).core := by
  dsimp only; unfold atomG Routes.atomRows HashRows.block; dsimp only
  refine catB (catB (catB ?_ ?_) (catB ?_ (catB ?_ ?_))) (catB (range_spec ..) (catB ?_ (catB (range_spec ..) (catB (range_spec ..) (catB (range_spec ..) ?_)))))
  all_goals first | apply prod_spec | apply add_spec | refine ⟨rfl,fun g w => ?_⟩; rw [eqs_local]
  all_goals intros; simp only [Routes.hash,Routes.elem,GateRoutes.word,HashRows.pub,HashRows.padded,regR,pinR,Ref.read] <;> split_ifs <;> simp_all [Ref.read,Fin.isLt]
private theorem stageFits {m d : ℕ} (hd : 1≤d) (p X : ℕ) (i : Fin (2*m-1)) : FitsG (stageG (List.replicate d ()) d p m X i) (Routes.stage hd p X i).core := by
  unfold stageG Routes.stage stageBlock stageProducts stageSum; dsimp only; refine catB (catB ?_ ?_) ?_
  all_goals first | apply prod_spec | apply add_spec
  all_goals intros; simp only [regR,pinR,Routes.elem,Routes.acc,GateRoutes.word,HashRows.pub,HashRows.padded,Ref.read] <;> split_ifs <;> simp_all [Routes.elem,Routes.acc,GateRoutes.word,HashRows.padded,HashRows.pub,Ref.read] <;> split_ifs <;> simp_all [Ref.read] <;> omega

/-- Decode a fixed-width seed coefficient; packet bits are stored most significant first. -/
private def coeff (b : ℕ) (s : W) (i k : ℕ) := PolyT.bval ((s.drop ((2*i+k)*b)).take b).reverse
private def body (q : List Unit) (b d e m p T X : ℕ) (s η : W) : GC :=
  catG ((Routes.bank m d e).size+1,fun _ _ => true) (catG (1,fun _ w => !w.getD 0 false)
    (catG (manyG (2*m) fun i => atomG q d p T (coeff b s (i%m) 0) (coeff b s (i%m) 1)) (catG (manyG (2*m-1) (stageG q d p m X)) (catG (manyG (2*m-2) fun _ => rangeG d p)
      (catG (1,fun _ _ => decide (η.length ≤ 2*m*b)) (η.length,fun i w => (if i/b/2 < m then w.getD 0 false else false) == η.getD i false))))))
private def code (w : W) := let p := FpPair.Packet.prime w; let b := S8G.FpMoment.Code.width p; let d := b+1
  body (CoreCheck.pad p) b d (wires d) (S8G.FpMoment.Code.slots b) p (FpPair.Packet.threshold w) (PolyT.bval (FpPair.Packet.target w)) (FpPair.Packet.seed w) (FpPair.Packet.prefixBits w)
private def check (z : S8H0.PortEval.Input) := if z.2.1 < (code z.1).1 then (code z.1).2 z.2.1 z.2.2 else S8H0.PortEval.agree z.2.2

/-- Evaluate the Boolean subdivision tensor at the vertex and bits in a tag-5 port query. -/
def port : W → W := S8C.portPacket check

private theorem coeff_ok {p m : ℕ} (S : FpSeed p m) (i : Fin m) (k : Fin 2) : coeff (bitLen p) (List.ofFn (fpBits S)) i k = fpWords S i k := by
  have h := S8C3.Packet.coeff_word 0 S i [] k
  obtain ⟨hp,_,hs,hi,_⟩ := S8C3.Packet.fields 0 S i []; simpa only [S8C3.Packet.coeff,hp,hs,hi,S8G.FpMoment.Code.width_eq,coeff] using h
private theorem atomPos (q : List Unit) (d p T : ℕ) : 0 < (atomG q d p T 0 0).1 := by dsimp only [atomG,catG,prodG,rangeG,addG,eqsG,mulG]; omega
private theorem stagePos (q : List Unit) (d p m : ℕ) (hd : 0<d) : 0 < (stageG q d p m 0 0).1 := by dsimp only [stageG,catG,prodG,addG,eqsG,mulG]; omega
private theorem atomSize (q : List Unit) (d p T a b : ℕ) : (atomG q d p T a b).1 = (atomG q d p T 0 0).1 := rfl
private theorem stageSize (q : List Unit) (d p m X j : ℕ) : (stageG q d p m X j).1 = (stageG q d p m 0 0).1 := rfl
private theorem digitRead (p m e k : ℕ) (x : Bool) : (Routes.digit (m:=m) (d:=bitLen p+1) (e:=e) p k).read x = (if k/bitLen p/2 < m then x else false) := by
  have hi : bitLen p-1-k%bitLen p < bitLen p+1 := by omega
  by_cases h : k/bitLen p/2 < m <;> simp [Routes.digit,h,Routes.elem,GateRoutes.word,HashRows.padded,hi,Ref.read]
private theorem codeFits {p : ℕ} [Fact p.Prime] (T : ℕ) (S : FpSeed p (blockCount (bitLen p))) (X : (ZMod p)ˣ) (η : W) : FitsG (code (FpPair.word T S X η)) (Semantics.core p _ T (X : ZMod p).val (AtomLift.coeff S) η) := by
  let b := bitLen p; let d := b+1; let m := blockCount b; let hd : 1≤d := Nat.succ_pos _
  obtain ⟨hp,ht,hs,hx,hη⟩ := FpPair.Packet.fields T S X η
  simp only [code,hp,ht,hs,hx,hη,decode_count,S8G.FpMoment.Code.width_eq,S8G.FpMoment.Code.slots_eq,pad_eq,wires_eq (Semantics.width_pos p)]
  unfold body; apply catG_spec (A:=⟨AnchoredLayout.anchors ((Semantics.shape p m).size+1),fun _ _ => true⟩) (B:=(Semantics.net p m T (X : ZMod p).val (AtomLift.coeff S) η).core) ⟨rfl,fun _ _ => rfl⟩
  unfold Semantics.net Routes.network Routes.prefixRows
  refine catB ⟨rfl,fun g w => (zeroLast_local _ g w).symm⟩ (catB ?_ (catB ?_ (catB ?_ (catB ?_ ?_))))
  · let s := List.ofFn (fpBits S); let f := fun i : ℕ => atomG (List.replicate d ()) d p T (coeff b s (i%m) 0) (coeff b s (i%m) 1)
    refine manyFits (atomPos (List.replicate d ()) d p T) f (Routes.atomRows hd p T (AtomLift.coeff S)) (fun i => atomSize ..) ?_; intro i; dsimp only [f,s]
    let j : Fin m := ⟨i%m,Nat.mod_lt _ (by have := i.isLt; change ↑i < 2*m at this; omega)⟩
    have ha : coeff b s (i%m) 0 = (S j).1.val+1 := coeff_ok S j (0 : Fin 2)
    have hb : coeff b s (i%m) 1 = (S j).2.val := coeff_ok S j (1 : Fin 2)
    change FitsG (atomG _ d p T (coeff b s (i%m) 0) (coeff b s (i%m) 1)) _; rw [ha,hb]; exact atomFits hd p T (AtomLift.coeff S) i
  · exact manyFits (stagePos (List.replicate d ()) d p m hd) (stageG (List.replicate d ()) d p m (X : ZMod p).val) (Routes.stage (m:=m) hd p (X : ZMod p).val) (fun i => stageSize ..) (fun i => stageFits hd p _ i)
  · exact manyFits (c:=d+1) (Nat.succ_pos _) (fun _ => rangeG d p) (fun i => RangeRows.checker p (Routes.intermediate (d:=d) (m:=m) (e:=Routes.G hd) i)) (fun _ => rfl) (fun _ => range_spec ..)
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp [m,b,(X : ZMod p).val_lt,(X : ZMod p).val_lt.trans (primeFitsAtom p),show blockCount (bitLen p) ≠ 0 by unfold blockCount; omega]
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; have hi : i.val < η.length := i.isLt
    simp only [digitRead,m,b,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]; rfl
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.length PolyT.getD PolyT.testBit PolyT.decide_lt PolyT.decide_eq PolyT.div PolyT.mod PolyT.reverse PolyT.take PolyT.drop CoreCheck.reorder_poly CoreCheck.column_poly CoreCheck.pad_poly w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly w4_M5Evaluator.clog2_poly S8G.FpMoment.Code.width_poly S8G.FpMoment.Code.slots_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219

open private Eff catP from Definitions.Def_DetDLP_S8C3_PortEval
variable {α : Type} [Enc α]
private theorem manyP {n : α → ℕ} {F : α → ℕ → GC} (hn : PolyT n) (h : ∀ {j : α → ℕ}, PolyT j → Eff fun x => F x (j x)) : Eff fun x => manyG (n x) (F x) := by
  have h0 := (h (PolyT.const 0)).1
  exact ⟨PolyT.mul hn h0,fun hi hw => (h (PolyT.div hi h0)).2 (PolyT.mod hi h0) hw⟩
private theorem atomP {q : α → List Unit} {d p T a b : α → ℕ} (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (ht : PolyT T) (ha : PolyT a) (hb : PolyT b) : Eff fun x => atomG (q x) (d x) (p x) (T x) (a x) (b x) := by
  unfold atomG prodG; refine catP (catP (catP (catP ?_ ?_) (catP ?_ ?_)) (catP ?_ (catP ?_ ?_))) (catP ?_ (catP ?_ (catP ?_ (catP ?_ (catP ?_ ?_)))))
  all_goals refine ⟨?_,fun hi hw => ?_⟩ <;> simp only [mulG,eqsG,addG,rangeG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem stageP {q : α → List Unit} {d p m X j : α → ℕ} (hq : PolyT q) (hd : PolyT d) (hp : PolyT p) (hm : PolyT m) (hx : PolyT X) (hj : PolyT j) : Eff fun x => stageG (q x) (d x) (p x) (m x) (X x) (j x) := by
  unfold stageG prodG; refine catP (catP (catP ?_ ?_) (catP ?_ ?_)) ?_
  all_goals refine ⟨?_,fun hi hw => ?_⟩ <;> simp only [mulG,eqsG,addG,regR,pinR] <;> fun_prop (disch := assumption)
private theorem bodyP {q : α → List Unit} {b d e m p T X : α → ℕ} {s η : α → W} (hq : PolyT q) (hb : PolyT b) (hd : PolyT d) (he : PolyT e) (hm : PolyT m) (hp : PolyT p) (ht : PolyT T) (hx : PolyT X) (hs : PolyT s) (hη : PolyT η) : Eff fun x => body (q x) (b x) (d x) (e x) (m x) (p x) (T x) (X x) (s x) (η x) := by
  unfold body; refine catP ?_ (catP ?_ (catP (manyP (by fun_prop) fun hj => atomP hq hd hp ht ?_ ?_) (catP (manyP (by fun_prop) fun hj => stageP hq hd hp hm hx hj) (catP (manyP (by fun_prop) fun _ => ?_) (catP ?_ ?_)))))
  all_goals first | unfold coeff; fun_prop (disch := assumption) | refine ⟨?_,fun hi hw => ?_⟩ <;> simp only [Routes.bank,Routes.atom,Routes.extra,RegisterMap.triple,RegisterMap.run,RegisterMap.mul,GateRoutes.auxShape,stageShape,Shape.size,rangeG,addG,regR,pinR] <;> fun_prop (disch := assumption)

/-- One polynomial-time algorithm handles every choice of packet parameters. -/
theorem port_poly : PolyT port := by
  let π := @Prod.fst W (ℕ × W); have hπ : PolyT π := PolyT.fst PolyT.id'
  have hp := PolyT.comp FpPair.Packet.prime_poly hπ; have hb := S8G.FpMoment.Code.width_poly hp; have hd := PolyT.add hb (PolyT.const 1)
  have hx : PolyT (fun z => PolyT.bval (FpPair.Packet.target (π z))) := by have h := PolyT.comp FpPair.Packet.target_poly hπ; fun_prop (disch := assumption)
  have H := bodyP (CoreCheck.pad_poly hp) hb hd (mul_poly.nb hd) (S8G.FpMoment.Code.slots_poly hb) hp (PolyT.comp FpPair.Packet.threshold_poly hπ) hx (PolyT.comp FpPair.Packet.seed_poly hπ) (PolyT.comp FpPair.Packet.prefix_poly hπ)
  apply S8C.portPacket_poly; exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt (PolyT.fst (PolyT.snd PolyT.id')) H.1) (H.2 (by fun_prop) (by fun_prop)) (PolyT.comp S8H0.PortEval.agree_poly (by fun_prop))

open w4_M5Network in
/-- On an encoded pair packet, the result is the singleton encoding of the local tensor value. -/
theorem port_eval {p : ℕ} [Fact p.Prime] (T : ℕ) (S : FpSeed p (blockCount (bitLen p))) (X : (ZMod p)ˣ) (η : W) (v : Fin (w3_factorGraph (Semantics.layout p _ T (X : ZMod p).val (fun i => ((S i).1.val+1,(S i).2.val)) η)).subdivision.nV) (a) :
    port (encodePortQuery (FpPair.word T S X η) v.val (List.ofFn a)) = encodeNatListBin [if (w3_factorGraph (Semantics.layout p _ T (X : ZMod p).val (fun i => ((S i).1.val+1,(S i).2.val)) η)).subdivisionTensor (w3_factorChecks _ (Semantics.tests p _ T (X : ZMod p).val (fun i => ((S i).1.val+1,(S i).2.val)) η)) v a then 1 else 0] := by
  let C := Semantics.core p _ T (X : ZMod p).val (AtomLift.coeff S) η; let W := Semantics.wiring p _ T (X : ZMod p).val (AtomLift.coeff S) η
  have H := codeFits T S X η; unfold port; rw [S8C.portPacket_eq]; suffices check (FpPair.word T S X η,v.val,List.ofFn a) = (G C W).subdivisionTensor (CircuitRealizes.T C W) v a by rw [this]; rfl
  unfold check; dsimp only; rw [H.1]; split
  · rename_i hv; let g : Fin C.A.ng := ⟨v.val,hv⟩; exact (H.2 g _).trans (core_tensor C W g a)
  · exact nonGate C W v a (by assumption)
end DetDLP.S8L.PortEval


