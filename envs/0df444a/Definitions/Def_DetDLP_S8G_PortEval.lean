-- Prove2me | Definitions.Def_DetDLP_S8G_PortEval
-- name    : DetDLP_S8G_PortEval
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:06:31.423891+00:00
-- url     : https://prove2.me/theorems/55ddcad2-a555-4505-af72-518a752d2865

import Definitions.Def_DetDLP_S8G_PortPoly
import Definitions.Def_DetDLP_S8G_Bounds
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8G.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap SeedAndAtomBank Routes FpAtomRows LocalGateEq PortPoly
abbrev port := PortPoly.packetPort
theorem port_poly : Groundwork.PolyT port := PortPoly.port_poly
private theorem tileFits {s : Shape} {n : ℕ} (g : GC) (b : Fin n → B (s.size+1)) (h : ∀ i, FitsG g (b i).core) : FitsG (tile n g) (allRows n b).core := by
  cases n with
  | zero => exact ⟨Nat.zero_mul _,fun i => Fin.elim0 i⟩
  | succ n => induction n with
    | zero => refine ⟨(Nat.one_mul _).trans (h 0).1,fun i w => ?_⟩; exact (congrArg (fun j => g.2 j w) (Nat.mod_eq_of_lt ((h 0).1.symm ▸ i.isLt))).trans ((h 0).2 i w)
    | succ n ih =>
      have H := catB (h 0) (ih (fun i => b i.succ) fun i => h i.succ)
      change FitsG _ (joinB (b 0) (allRows (n+1) fun i => b i.succ)).core
      refine ⟨(Nat.succ_mul _ _).trans ((Nat.add_comm ..).trans H.1),fun i w => ?_⟩
      rw [←H.2 i w]; simp only [tile,catG]; split_ifs with hi
      · rw [Nat.mod_eq_of_lt hi]
      · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi); simp [hk]
private theorem orFits {s : Shape} (n : ℕ) (x t : Fin n → Ref s) (b : Ref s) (f : Bool)
    (hx : ∀ i y, (x i).read y = y) (ht : ∀ i y, (t i).read y = y) (hb : ∀ y, b.read y = (f && y)) : FitsG (orG n f) (orRows n x b t).core := by
  induction n generalizing b f with
  | zero => rw [orRows.eq_1]; refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp [orG,Fin.eq_zero i,hb]
  | succ n ih =>
    let g : GC := (1,fun _ w => decide (w.getD 2 false = ((f && w.getD 0 false) || w.getD 1 false)))
    have h : FitsG g (rows 1 3 (fun _ => ![b,x 0,t 0]) (fun _ v => decide (v 2 = (v 0 || v 1)))).core := by
      refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp [g,hb,ht,hx]
    have H := catB h (ih (x ∘ Fin.succ) (t ∘ Fin.succ) (t 0) true (fun i => hx _) (fun i => ht _) (by simp [ht]))
    rw [orRows]; refine ⟨by simpa only [catG,g,orG,Nat.add_comm] using H.1,fun i w => ?_⟩
    rw [←H.2 i w]; simp only [catG,g,orG]; by_cases hz : i.val = 0
    · simp [hz]
    · have h1 : ¬i.val<1 := by omega
      have he : i.val<n+1 ↔ i.val-1<n := by omega
      have hne : (i.val != 0) = true := bne_iff_ne.mpr hz
      simp [h1,hne,he]
private theorem seedFits {s : Shape} {d : ℕ} (p : ℕ) (q : GateRoutes.Path (seedSlot d) s) : FitsG (seedG d p) (seedSlotBlock p q).core := by
  refine catB (range_spec ..) (catB (range_spec ..) (add_spec _ ?_ ?_ ?_ ?_))
  all_goals intros; simp [seedA,GateRoutes.word,HashRows.pub,HashRows.padded,regR,pinR,Ref.read] <;> split_ifs <;> simp_all [Ref.read]
set_option backward.isDefEq.respectTransparency true in
private theorem atomFits {s : Shape} {d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (A B : HashRows.Word s)
    (q : GateRoutes.Path (atomSlot d (edges hd)) s)
    (ha : ∀ k x, (A k).read x = regR d k x)
    (hb : ∀ k x, (B k).read x = regR d k x) :
    FitsG (atomG (List.replicate d ()) d p T) (atomSlotBlock hd p T A B q).core := by
  unfold atomG atomSlotBlock; dsimp only
  refine catB (range_spec ..) (catB (orFits _ _ _ _ _ ?_ (fun _ _ => rfl) (fun _ => rfl)) (catB (range_spec ..) (catB (range_spec ..) (catB (range_spec ..) ?_))))
  · intros; simp only [GateRoutes.word,HashRows.padded,dif_pos (Fin.isLt _),Ref.read]
  unfold genHashG HashRows.block; dsimp only
  have hm (i : Fin (w3_fpMulLayout d hd).nb) : i.val < edges hd := i.isLt
  simp only [GateRoutes.word, HashRows.padded, hm, dif_pos]
  refine catB (catB (prod_spec hd ?_ ?_ ?_) (prod_spec hd ?_ ?_ ?_)) (catB (add_spec _ ?_ ?_ ?_ ?_) (catB (add_spec _ ?_ ?_ ?_ ?_) (add_spec _ ?_ ?_ ?_ ?_)))
  all_goals intros; first | exact (ha _ _).symm | exact (hb _ _).symm | (simp only [seedA,seedB,GateRoutes.word,HashRows.pub,HashRows.padded,regR,pinR,Ref.read]; try (split_ifs <;> simp_all [Ref.read]))
private theorem stageFits {s : Shape} {d n : ℕ} (hd : 1 ≤ d) (p : ℕ) (x : HashRows.Word s)
    (ys : Fin n → HashRows.Word s) (zOut : HashRows.Word s) (q : GateRoutes.Path (chainShape n d (edges hd)) s)
    (i : Fin n) (hx : ∀ k b, (x k).read b = regR d k b)
    (hy : ∀ j k b, (ys j k).read b = regR d k b)
    (hz : ∀ k b, (zOut k).read b = regR d k b) :
    FitsG (stageG (List.replicate d ()) d p) (stageAt hd p x ys zOut q i).core := by
  unfold stageG stageAt stageBlock stageProducts stageSum; dsimp only
  have hm (k : Fin (w3_fpMulLayout d hd).nb) : k.val < edges hd := k.isLt
  simp only [GateRoutes.word, HashRows.padded, hm, dif_pos]
  refine catB (catB (prod_spec hd ?_ ?_ ?_) (prod_spec hd ?_ ?_ ?_)) (add_spec _ ?_ ?_ ?_ ?_)
  all_goals intros; (try simp only [residueWord,GateRoutes.word,HashRows.pub,HashRows.padded]); (try split_ifs) <;> (try rw [hx]) <;> (try rw [hy]) <;> (try rw [hz]) <;> (try simp only [residueWord,GateRoutes.word,HashRows.padded,regR,pinR,Ref.read]) <;> (try split_ifs) <;> (try simp_all [Ref.read])
private theorem fits (p m : ℕ) (hm : 2 ≤ m) (j : Fin 4) (T : ℕ) (η : W) : let b := bitLen p; let d := b+1; let hd : 1≤d := Nat.succ_pos _; let N := Semantics.net p m j T η
    FitsG (tree (List.replicate d ()) b m p T (copies j) (outputs j) (edges hd) η) (AnchoredLayout.block N.core ((Semantics.shape p m j).size+1)) := by
  dsimp only; unfold tree; apply catG_spec (A:=⟨AnchoredLayout.anchors _,fun _ _ => true⟩) (B:=(Semantics.net p m j T η).core)
  · refine ⟨?_,fun _ _ => rfl⟩; simp only [anchorCount,anchorsG,Semantics.shape,Routes.bank,productShape,Shape.size,AnchoredLayout.anchors]; omega
  refine catB ⟨rfl,fun g w => (zeroLast_local _ g w).symm⟩ ?_
  unfold Routes.network seedBlock; refine catB (catB (tileFits _ _ fun _ => seedFits ..) ?_) (catB (tileFits _ _ fun k => tileFits _ _ fun i => atomFits (d:=bitLen p+1) (Nat.succ_pos _) p T (coeffA i) (coeffB i) (fun a => atoms (e:=edges (Nat.succ_pos _)) k (.vec i a)) (by intros; simp only [coeffA,seedA,GateRoutes.word,HashRows.padded,regR]; split_ifs <;> simp_all [Ref.read] <;> omega) (by intros; simp only [coeffB,seedB,GateRoutes.word,HashRows.padded,regR]; split_ifs <;> simp_all [Ref.read] <;> omega)) (tileFits _ _ fun t => catB (range_spec ..) (tileFits _ _ fun k => ?_)))
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; by_cases h : i.val < m*2*bitLen p
    · have read (a : Fin (bitLen p)) (y : Bool) (q : GateRoutes.Path (seedSlot (bitLen p+1)) (Semantics.shape p m j)) : (seedA q a).read y = y ∧ (seedB q a).read y = y := by
        have ha : a.val < bitLen p+1 := by omega
        simp only [seedA,seedB,GateRoutes.word,HashRows.padded,dif_pos ha,Ref.read,and_self]
      simp only [rowsG,prefixBit,dif_pos h,true_and,h,List.getD_eq_getElem _ _ i.isLt]; split_ifs <;> simp only [(read ..).1,(read ..).2] <;> rfl
    · simp [rowsG,h]
  · unfold chainBlock; refine catB ?_ (catB (tileFits _ _ fun _ => range_spec ..) (tileFits _ _ fun i => stageFits (d:=bitLen p+1) (n:=m-1) (Nat.succ_pos _) p (initial k) (tail k) (residueWord (result t)) (stages (e:=edges (Nat.succ_pos _)) t k) i (by intro k1 b1; unfold initial; rw [dif_pos (by omega : 0 < m)]; simp only [Routes.atom,residueWord,GateRoutes.word,HashRows.padded,regR]; try (split_ifs <;> simp_all [Ref.read])) (by intro j1 k1 b1; simp only [Routes.tail,Routes.atom,residueWord,GateRoutes.word,HashRows.padded,regR]; try (split_ifs <;> simp_all [Ref.read])) (by intro k1 b1; simp only [residueWord,GateRoutes.word,HashRows.padded,regR]; try (split_ifs <;> simp_all [Ref.read]))))
    have h : m-1 ≠ 0 := by omega
    exact ⟨by simp [h,rows,mapped],fun i => Fin.elim0 (i.cast (by simp [h,rows,mapped]))⟩
open w4_M5Network in
/-- The encoded port response is the subdivision tensor bit for every branch and local assignment. -/
theorem port_eval (p : ℕ) (j : Fin 4) (T : ℕ) (η : W) : let m := blockCount (bitLen p); let A := Semantics.layout p m j T η
    ∀ (v : Fin (w3_factorGraph A).subdivision.nV) a, port (encodePortQuery (FpMoment.word p j T η) v.val (List.ofFn a)) = encodeNatListBin [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A (Semantics.tests p m j T η)) v a then 1 else 0] := by
  dsimp only; intro v a; apply fullPort_eval (F:=decoded) (AnchoredLayout.block (Semantics.net ..).core _) (AnchoredLayout.wiring (Semantics.net ..).core (Semantics.net ..).name)
  obtain ⟨hp,hj,hT,hη⟩ := FpMoment.Code.fields p j T η
  unfold decoded; simp only [hp,hj,hT,hη,FpMoment.Code.width_eq,FpMoment.Code.slots_eq,pad_eq,S8H.PointAddresses.wires_eq (Nat.succ_pos _)]
  have hm : 2 ≤ blockCount (bitLen p) := le_max_left ..
  simpa only [copies,outputs,Fin.ext_iff,show (3 : Fin 4).val = 3 from rfl,GateSemantics.d,edges] using fits p _ hm j T η
end DetDLP.S8G.PortEval


