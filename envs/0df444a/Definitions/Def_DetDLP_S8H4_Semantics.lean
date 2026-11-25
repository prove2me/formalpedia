-- Prove2me | Definitions.Def_DetDLP_S8H4_Semantics
-- name    : DetDLP_S8H4_Semantics
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:18:39.165587+00:00
-- url     : https://prove2.me/theorems/48f4e200-70c9-40df-abd2-5cd77525a676
-- title:
--   Tag 4 anchored layout, EC element bijection, and graph bounds
-- statement:
--   The anchored tag 4 layout fixes its final register to zero. For a prime $p$ and $T\le p$, its satisfying assignments correspond bijectively to points of $E$ satisfying `elemPin`. The parity of the $y$-coordinate determines the two seed words, and the seventh hash row supplies the value compared with $T$.
--
--   Let $b=\operatorname{bitLen}(p)$ and $s=\texttt{OrderPacket.scale}(b)$. For $|\eta|\le 2b+1$, the gate and edge counts satisfy $n_g\le s$ and $2n_e<s$. Every factor-graph vertex has degree at most $\max\{12,\lceil136(b+2)^{3/4}\rceil\}$ regardless of prefix length.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_Routes
import Definitions.Def_DetDLP_S8H0_GraphDegree
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
namespace DetDLP.S8H4.Semantics
open S8H0 RegisterMap NamedBlocks GateSemantics S8J.CircuitRealizes GateRoutes
open S8J ResidueWires SignalBank GraphDegree S8H ECPointArithmetic ECPointSlots
private abbrev bank (p : ℕ) := Routes.bank (d p) (e p)
variable (p T a0 b0 a1 b1 : ℕ) (c : Coeff) (η : List Bool)
private def net := joinB (PointGraph.zeroLast (bank p).size) (Routes.network (hd p) p T a0 b0 a1 b1 c η)
private abbrev Bk := AnchoredLayout.block (net p T a0 b0 a1 b1 c η).core ((bank p).size+1)
private abbrev W := AnchoredLayout.wiring (net p T a0 b0 a1 b1 c η).core (net p T a0 b0 a1 b1 c η).name
def layout : w3_FactorLayout := circuit (Bk p T a0 b0 a1 b1 c η) (W p T a0 b0 a1 b1 c η)
def tests : w3_factorTest (layout p T a0 b0 a1 b1 c η) := test (Bk p T a0 b0 a1 b1 c η) (W p T a0 b0 a1 b1 c η)
noncomputable section
variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (i : Fin m)
private abbrev V {p : ℕ} (u : Bits ((bank p).size+1)) := (bank p).decode (u ∘ Fin.castSucc)
private def pick (w : (GateRoutes.S (d p) (e p)).Data) := S i ((value w.1.2.2.1).val.testBit 0)
private def valid (v : (bank p).Data) := canonical p v.1 ∧ ∀ j : Fin (d p),
  v.2.1 j = ((pick S i v.1).1.val+1).testBit j ∧ v.2.2.1 j = (pick S i v.1).2.val.testBit j
private def unpack : {v // valid S i v} ≃ ECPointSlots.C p × (Transcript p × w3_slotDiff (d p)) := by
  let f : {v // valid S i v} ≃ {w // canonical p w} × w3_slotDiff (d p) :=
    { toFun := fun v => (⟨v.val.1,v.prop.1⟩,value v.val.2.2.2.1,v.val.2.2.2.2)
      invFun := fun ⟨w,z,k⟩ => ⟨(w.val,(fun j => ((pick S i w.val).1.val+1).testBit j),(fun j => (pick S i w.val).2.val.testBit j),(numBits _).symm z,k),w.prop,fun _ => ⟨rfl,rfl⟩⟩
      left_inv := fun v => Subtype.ext (Prod.ext rfl (Prod.ext (funext fun j => (v.prop.2 j).1.symm) (Prod.ext (funext fun j => (v.prop.2 j).2.symm) (Prod.ext ((numBits _).symm_apply_apply _) rfl))))
      right_inv := fun ⟨_,_,_⟩ => Prod.ext rfl (Prod.ext ((numBits _).apply_symm_apply _) rfl) }
  exact f.trans ((SignalBank.decode.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc ..))
private abbrev old {p : ℕ} (u : Bits ((bank p).size+1)) : U p := u ∘ Routes.network.embed
private theorem old_eq {p : ℕ} (u : Bits ((bank p).size+1)) : raw (old u) = (V u).1 := by
  apply congrArg ((GateRoutes.S (d p) (e p)).decode); funext j; exact congrArg u (Fin.lastCases_castSucc j)
private theorem six (u : Bits ((bank p).size+1)) (h : valid S i (V u)) :
    let t := unpack S i ⟨V u,h⟩; let y := t.1.2.2
    (HashRows.block p (Routes.network.six (hd p) p (coeff E))).OK u ↔ w3_slotHashBits (hd p) (alpha S i y).val (beta S i y).val t.1.2.1.val (t.2.1.1 6).1.val (t.2.1.1 6).2 (t.2.1.2 6) := by
  let v := V u; let t := unpack S i ⟨v,h⟩; let y := t.1.2.2
  have Y : y.val = (value v.1.1.2.2.1).val := resVal _ _
  have P : pick S i v.1 = S i (decide (y.val % 2 = 1)) := by rw [pick,Nat.testBit_zero,Y]
  have A : (alpha S i y).val = ((pick S i v.1).1.val+1) := by rw [P,alpha,ZMod.val_natCast_of_lt]; have := (S i (decide (y.val % 2 = 1))).1.isLt; omega
  have B : (beta S i y).val = (pick S i v.1).2.val := by rw [P,beta,ZMod.val_natCast_of_lt (S i _).2.isLt]
  have digit (z : ZMod p) (w : Bits (d p)) (hw : ∀ j : Fin (d p), w j = z.val.testBit j) : (value w).val = z.val := by
    exact congrArg Fin.val (show numBits _ w = ⟨z.val,z.val_lt.trans (fits p)⟩ from (numBits _).eq_symm_apply.mp (funext hw))
  have a := digit (alpha S i y) v.2.1 (fun j => A ▸ (h.2 j).1); have b := digit (beta S i y) v.2.2.1 (fun j => B ▸ (h.2 j).2)
  have x : t.1.2.1.val = (value v.1.1.2.1.1).val := resVal _ _
  have z : (t.2.1.1 6).1.val = (value (v.1.2.1 6).1.1).val := resVal _ _
  have r : (t.2.1.1 6).2.1.1.val = (value (v.1.2.1 6).2.1.1.1).val := finEquiv_val _ _
  have L {n} (f : Ref (GateRoutes.S (d p) (e p)) → Ref (bank p)) (hf : ∀ q, f (.reg q) = .reg (.fst q)) (h0 : f (.pin false) = .pin false) (l : GateRoutes.Path (.word n) (GateRoutes.S (d p) (e p))) (w : Bits n) (hw : ∀ j, (l (.word j)).get v.1 = w j) : HashRows.evalWord (f ∘ GateRoutes.word l) u (value w) := by
    intro j; have J := GateRoutes.word_eval (fun q => .fst (l q) : GateRoutes.Path (.word n) (bank p)) u w hw j
    convert J using 1; unfold GateRoutes.word HashRows.padded; dsimp only [Function.comp_apply]; split <;> simp only [hf,h0] <;> rfl
  refine HashRows.block_spec (hd p) _ u _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals dsimp only [Routes.network.six,wires,rword,GateRoutes.quot,Routes.network.coord]
  all_goals first | rw [←a]; exact GateRoutes.word_eval (fun j => .snd (.fst j)) u _ (fun _ => rfl) | rw [←b]; exact GateRoutes.word_eval (fun j => .snd (.snd (.fst j))) u _ (fun _ => rfl) | rw [x]; apply GateRoutes.word_eval; intro; rfl | (funext j; exact (Ref.correct _ _).symm) | skip
  all_goals first | rw [z]; apply L _ (fun _ => rfl) rfl; intro; rfl | rw [r]; apply L _ (fun _ => rfl) rfl; intro; rfl | apply L _ (fun _ => rfl) rfl; intro; rfl | skip
  · intro j; rw [←Ref.correct]; change (p.testBit j && (v.1.2.1 6).2.2) = (@ite ℕ ((v.1.2.1 6).2.2 = true) (instDecidableEqBool _ _) p 0).testBit j
    cases (v.1.2.1 6).2.2 <;> simp; rfl
private theorem consInit {A : Type} {n : ℕ} {f g : Fin (n+1) → A} (a : A) (h : ∀ j : Fin n, f j.castSucc = g j.castSucc) (j : Fin (n+1)) : Matrix.vecCons a f j.castSucc = Matrix.vecCons a g j.castSucc := by
  induction j using Fin.cases with | zero => rfl | succ j => rw [←Fin.succ_castSucc,Matrix.cons_val_succ,Matrix.cons_val_succ]; exact h j
private theorem sameInit {A : Type} (q r s t u v a b : A) (j : Fin 6) :
    ![q,r,s,t,u,v,a] j.castSucc = ![q,r,s,t,u,v,b] j.castSucc := consInit q (consInit r (consInit s (consInit t (consInit u (consInit v (fun k => Fin.elim0 k)))))) j
private theorem firstSix (q : ECPointSlots.C p) (t : Transcript p) (a b : ZMod p) (j : Fin 6) :
    SevenChecks.gateArgs E q t j.castSucc = args E q.2.1 q.2.2 a b (fun g => (t.1 g).1) j.castSucc := sameInit _ _ _ _ _ _ _ _ j
private theorem decoded (u : Bits ((bank p).size+1)) :
    (Routes.network (hd p) p T ((S i false).1.val+1) (S i false).2.val ((S i true).1.val+1) (S i true).2.val (coeff E) η).OK u ↔
    ∃ h : valid S i (V u), elemOK E S i T (bitLen p) η (unpack S i ⟨V u,h⟩) := by
  refine (Routes.network_iff ..).trans ?_; let v := V u
  have mux : (∀ j : Fin (d p), v.2.1 j = (if (value v.1.1.2.2.1).val.testBit 0 then (S i true).1.val+1 else (S i false).1.val+1).testBit j ∧ v.2.2.1 j = (if (value v.1.1.2.2.1).val.testBit 0 then (S i true).2.val else (S i false).2.val).testBit j) ↔ ∀ j : Fin (d p), v.2.1 j = ((pick S i v.1).1.val+1).testBit j ∧ v.2.2.1 j = (pick S i v.1).2.val.testBit j := by unfold pick; cases (value v.1.1.2.2.1).val.testBit 0 <;> rfl
  have H (h : valid S i v) := six E S i u h
  have bridge (h : valid S i v) : let t := unpack S i ⟨v,h⟩; let args' := args E t.1.2.1 t.1.2.2 (alpha S i t.1.2.2) (beta S i t.1.2.2) (fun j => (t.2.1.1 j).1)
      (∀ j : Fin 6, (HashRows.block p (wires (hd p) p (coeff E) j.castSucc)).OK (old u) ↔ w3_slotHashBits (hd p) (args' j.castSucc).1.val (args' j.castSucc).2.2.val (args' j.castSucc).2.1.val (t.2.1.1 j.castSucc).1.val (t.2.1.1 j.castSucc).2 (t.2.1.2 j.castSucc)) ∧ (CurveRows.rawCheck v.1 ↔ checkCurve t.1 t.2.1) := by
    let hc : canonical p (raw (old u)) := (old_eq u).symm ▸ h.1
    let t := unpack S i ⟨v,h⟩; have D : typed (old u) hc = (t.1,t.2.1) := congrArg SignalBank.decode (Subtype.ext (old_eq u))
    constructor
    · intro j; have J := hash_iff E (old u) hc j.castSucc; dsimp only at J; rw [D,firstSix E t.1 t.2.1 (alpha S i t.1.2.2) (beta S i t.1.2.2)] at J; exact J
    · have J := PointGraph.curve_iff (old u) hc; rw [D,old_eq u] at J; exact J
  have tail' (h : valid S i v) : let t := unpack S i ⟨v,h⟩; (t.2.1.1 6).1.val = (value (v.1.2.1 6).1.1).val ∧ word (bitLen p) t.1 = v.1.1.1 :: (M89S1.digitWord (bitLen p) (value v.1.1.2.1.1) ++ M89S1.digitWord (bitLen p) (value v.1.1.2.2.1)) := by
    refine ⟨resVal _ _,congrArg₂ List.cons rfl (congrArg₂ List.append (congrArg (M89S1.digitWord _) ?_) (congrArg (M89S1.digitWord _) ?_))⟩ <;> exact resVal _ _
  constructor
  · rintro ⟨⟨hc,hg,hr⟩,hs,hm,hf,hl,hp⟩; let h : valid S i v := ⟨hc,mux.mp hm⟩
    exact ⟨h,Fin.lastCases ((H h).mp hs) (fun j => ((bridge h).1 j).mp (hg j)),(bridge h).2.mp hr,hf,(tail' h).1.symm ▸ hl,(tail' h).2.symm ▸ hp⟩
  · rintro ⟨h,hg,hr,hf,hl,hp⟩; exact ⟨⟨h.1,fun j => ((bridge h).1 j).mpr (hg j.castSucc),(bridge h).2.mpr hr⟩,(H h).mpr (hg 6),mux.mpr h.2,hf,(tail' h).1 ▸ hl,(tail' h).2 ▸ hp⟩
noncomputable def points {p m : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]
    {T : ℕ} (hT : T ≤ p) (S : ECSeed p m) (i : Fin m) (η : List Bool) :
    let a0 := (S i false).1.val + 1; let b0 := (S i false).2.val
    let a1 := (S i true).1.val + 1; let b1 := (S i true).2.val; let c := coeff E
    {x : Fin (layout p T a0 b0 a1 b1 c η).nb → Bool // ∀ g, tests p T a0 b0 a1 b1 c η g
      (fun e => x ((layout p T a0 b0 a1 b1 c η).bit e.1)) = true} ≃
      {P : E.toAffine.Point // ECPointGadget.elemPin (bitLen p) T S i η P = true} := by
  let dec := PointGraph.dropLast.trans (bank p).decode
  refine (w3_factorEquiv _ _).symm.trans ((S8J.CircuitRealizes.decode _ _).trans ((AnchoredLayout.assignments _ _).trans ?_))
  refine (Equiv.subtypeEquivRight (q := fun u => ∃ h : u (Fin.last _) = false, ∃ hv : valid S i (dec ⟨u,h⟩), _) ?_).trans ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm.trans ((Equiv.subtypeEquivOfSubtype dec).trans ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm.trans ((Equiv.subtypeEquivOfSubtype (unpack S i)).trans (elemEquiv w3_m5_modmul_r2 S i T _ hT η)))))
  intro u; change (net ..).OK u ↔ _; rw [net,joinB_iff,PointGraph.zeroLast_iff,decoded]; exact ⟨fun h => ⟨h.1,h.2⟩,fun ⟨h,k⟩ => ⟨h,k⟩⟩
end
open GraphBudget w4_M5GraphBounds w4_MulParams S8H.PointAddresses RangeRows
private theorem counts : let N := net p T a0 b0 a1 b1 c η
    N.core.A.ne = sizeE (d p) (e p) + 8*d p + 6 + η.length ∧
    N.core.A.ng = sizeG (d p) (graph (d p) (hd p)).nV + 2*d p + 2 + η.length := by
  constructor <;> simp only [net,Routes.network,RangeRows.block,CurveRows.block,HashRows.block,many,joinB,HashRows.product,eqs,HashRows.sumRows,checker,NamedBlocks.add,rows,mapped,join,S8C.AddLayout.layout,PointGraph.zeroLast,AnchoredLayout.anchors,w3_fpMulLayout,w3_m5Layout,w3_forgetSides,sizeE,sizeG,e] <;> omega
private theorem bankSize : (bank p).size = regs (d p)+4*d p+1 := by
  change (GateRoutes.S (d p) (e p)).size + (d p + (d p + (d p + (d p+1)))) = _; rw [anchorSize]; omega
theorem gateBudget (hη : η.length ≤ 2 * bitLen p + 1) : (layout p T a0 b0 a1 b1 c η).ng ≤ OrderPacket.scale (bitLen p) := by
  let N := net p T a0 b0 a1 b1 c η; change ((bank p).size+1+N.core.A.ng)+((bank p).size+1+N.core.A.ne) ≤ _
  have H := counts p T a0 b0 a1 b1 c η; rw [H.1,H.2,bankSize]; have := regs_linear (hd p); have := graph_edge_bound (hd p); have := baseV (hd p)
  simp only [sizeE,sizeG,e,d,OrderPacket.scale,ECPointArithmetic.width] at *; omega
theorem edgeBudget (hη : η.length ≤ 2 * bitLen p + 1) : 2 * (layout p T a0 b0 a1 b1 c η).ne < OrderPacket.scale (bitLen p) := by
  let K := (bank p).size+1+(net p T a0 b0 a1 b1 c η).core.A.ne; change 2*(K+(K+K)) < _; dsimp only [K]
  rw [(counts p T a0 b0 a1 b1 c η).1,bankSize]; have := regs_linear (hd p); have := graph_edge_bound (hd p)
  simp only [sizeE,e,d,OrderPacket.scale,ECPointArithmetic.width] at *; omega
private theorem boundedNet : good (net p T a0 b0 a1 b1 c η) (cap p) := by
  have R {s : Shape} {n m : ℕ} (hm : m ≤ 12) (r : Fin n → Fin m → Ref s) (t) := mono (row_ok _ _ r t) (small p m hm)
  have A {s : Shape} {n} (cin : Bool) (a b z k : Fin n → Ref s) := mono (add_ok cin a b z k) (small p 5 (by decide))
  have H {s : Shape} (w : HashRows.Wires (d p) (hd p) s) : good (HashRows.block p w) (cap p) := by
    unfold HashRows.block HashRows.product; refine join_ok _ _ (join_ok _ _ (join_ok _ _ (mul_ok p _) ?_) (join_ok _ _ (mul_ok p _) ?_)) (join_ok _ _ (A _ _ _ _ _) (join_ok _ _ (A _ _ _ _ _) (A _ _ _ _ _))) <;> exact R (by decide) _ _
  have base : good (RangeRows.block (d p) (e p) p) (cap p) := by
    unfold RangeRows.block; exact join_ok _ _ (join_ok _ _ (A _ _ _ _ _) (A _ _ _ _ _)) (many_ok _ _ fun _ => join_ok _ _ (A _ _ _ _ _) (A _ _ _ _ _))
  unfold net Routes.network
  refine join_ok _ _ (anchors_ok 1 _ (small p 1 (by decide))) (join_ok _ _ ?_ (join_ok _ _ (H _) (join_ok _ _ (R (by decide) _ _) (join_ok _ _ (R (by decide) _ _) (join_ok _ _ (A _ _ _ _ _) (R (by decide) _ _))))))
  exact join_ok _ _ base (join_ok _ _ (many_ok _ _ fun _ => H _) (R (m:=5) (by decide) _ _))
theorem degree (v : Fin (w3_factorGraph (layout p T a0 b0 a1 b1 c η)).nV) :
    (w3_factorGraph (layout p T a0 b0 a1 b1 c η)).deg v ≤ max 12 (Nat.ceil (136 * ((bitLen p : ℝ) + 2) ^ ((3 : ℝ) / 4))) := by
  let A := (Bk p T a0 b0 a1 b1 c η).A; let N := net p T a0 b0 a1 b1 c η; let f := AnchoredLayout.signal N.core N.name
  have h : bounded A (cap p) := by
    intro j; induction j using Fin.addCases with
    | left j => simpa [A,Bk,AnchoredLayout.block,join] using anchors_ok ((bank p).size+1) _ (small p 1 (by decide)) j
    | right j => simpa [A,Bk,AnchoredLayout.block,join] using boundedNet p T a0 b0 a1 b1 c η j
  induction v using Fin.addCases with
  | left i => induction i using Fin.addCases with
              | left i => exact (NamedWires.oldDegree f A.gate i).le.trans (h i)
              | right i => exact (NamedWires.eqDegree f A.gate i).le.trans (small p 2 (by decide))
  | right i => exact (CopyCycle.bitDegree A.gate (NamedWires.next f) i).le.trans (small p 3 (by decide))
end DetDLP.S8H4.Semantics


