-- Prove2me | Definitions.Def_DetDLP_M3B_ECNetBijection
-- name    : DetDLP_M3B_ECNetBijection
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:57:27.310512+00:00
-- url     : https://prove2.me/theorems/1402ffcb-498f-45f7-92db-cb0ba660fb72
-- title:
--   Physical acceptance bijection for the native elliptic-curve network
-- statement:
--   Physical assignments satisfying all arithmetic, lookup-bus and prefix rows are in bijection with endpoint-correct, prefix-correct tuples. The forward map is the physical tuple decoder, and erasing the unique joined witness agrees with the checked-table certificate equivalence.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECSliceLift

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace DetDLP.M3B.ECNetBijection
open S8H0 RegisterMap NamedBlocks HashRows GateRoutes ResidueWires SignalBank GateSemantics
open S8H.ECPointArithmetic S8K.ECAddArithmetic ECCert ECPhysicalNet ECArithBlock ECSliceLift ECMapRows ECChainBlocks
variable {p m k : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]
variable {seed : ECSeed p m} {T : ℕ} {b : Fin m}

noncomputable def slotTyped (w : Slot E seed T b) : S8H.ECPointSlots.C p × S8H.ECPointSlots.Transcript p :=
  ((!ECAddrGadget.odd w,w.1.1.2),w.1.2.1)
noncomputable def slotData (a : ECArithNet.Checked E seed T k b) : (SlotCell p k).Data :=
  ((SignalBank.decode.symm (slotTyped a.1.1)).val, (numBits _).symm a.1.1.1.2.2.1, a.1.1.1.2.2.2,
    ![a.1.2.1,a.1.2.2.1,a.1.2.2.2])

private def pairIx : Fin m × Fin 2 ≃ Fin (2*m) where
  toFun a := pointIdx a.1 a.2
  invFun j := (⟨j.val/2,by omega⟩,⟨j.val%2,by omega⟩)
  left_inv a := Prod.ext (Fin.ext (by simp [pointIdx]; omega)) (Fin.ext (by simp [pointIdx]; omega))
  right_inv j := Fin.ext (by simp [pointIdx]; omega)
private def sideIx : Fin (2*m) × Bool ≃ Fin (4*m) where
  toFun a := ix a.2 a.1
  invFun j := (⟨j.val/2,by omega⟩, decide (j.val%2=1))
  left_inv := by rintro ⟨j,b⟩; cases b <;> simp [ix,Fin.ext_iff] <;> omega
  right_inv j := Fin.ext (by change 2*(j.val/2)+(decide (j.val%2=1)).toNat=j.val; by_cases h : j.val%2=1 <;> simp [h] <;> omega)
private theorem owner (b : Fin m) (j : Fin 2) (s : Bool) : (ix s (pointIdx b j)).val/4=b.val := by cases s <;> simp [ix,pointIdx] <;> omega
private theorem slotsAll {D : Fin (4*m) → Prop} (h : ∀ b j s, D (ix s (pointIdx b j))) : ∀ i, D i := by
  intro i; obtain ⟨⟨q,s⟩,rfl⟩ := (sideIx (m:=m)).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (pairIx (m:=m)).surjective q; exact h b j s

variable (v : Bits ((ShapeOf p m k).size+1)) (i : Fin (4*m)) (hb : i.val/4 = b.val)
private theorem at_slotBank : At (slot i) v (raw (v ∘ (slotPath i).bank)) := fun j =>
  (congrArg v (bankName_index i j).symm).trans (Addr.correct j ((v ∘ (slotPath i).bank) ∘ Fin.castSucc)).symm
private theorem neg_value (u : U p) (h : canonical p (raw u)) : negRef.eval u = (typed u h).1.1 :=
  (Addr.correct CurveRows.flag (u ∘ Fin.castSucc)).symm

theorem checkedSlot_at (hs : (slotAt E seed T i).OK v) (ha : (ECArithNet.bank inputs T).OK v) :
    At (cell i) v (slotData (checkedSlot E seed T v i b hb hs ha)) := by
  let a := checkedSlot E seed T v i b hb hs ha
  let z : SlotPath p (ShapeOf p m k) := slotPath i
  let u := v ∘ z.bank
  have eq : (⟨i.val/4,by omega⟩ : Fin m) = b := Fin.ext hb
  have hs' : (slotBlock E seed b T z).OK v := eq ▸ hs
  have H := (slotBlock_iff E seed b T z v (hash_route i v)).mp hs'
  let h := H.2.choose
  have flag : (typed u h).1.1 = !ECAddrGadget.odd a.1.1 := by
    rw [← neg_value, H.2.choose_spec.1, parity_value u h]; rfl
  have ht : typed u h = slotTyped a.1.1 := Prod.ext (Prod.ext flag rfl) rfl
  have hr : (decode.symm (slotTyped a.1.1)).val = raw u := by
    rw [← ht]; exact congrArg Subtype.val (decode.symm_apply_apply _)
  have hd : (numBits _).symm a.1.1.1.2.2.1 = (fun j => (z.diff j).eval v) := (numBits _).symm_apply_apply _
  have hr' := read_of_at (at_slotBank v i)
  apply (show readPath (cell i) v = slotData a → At (cell i) v (slotData a) from fun he => he ▸ at_read _ _)
  apply Prod.ext (hr'.trans hr.symm)
  apply Prod.ext hd.symm
  apply Prod.ext
  · rfl
  funext j; fin_cases j <;> rfl

private theorem slotView (a : ECArithNet.Checked E seed T k b) (H : At (cell i) v (slotData a)) :
    let u := v ∘ (slotPath i).bank
    ∃ h : canonical p (raw u), typed u h = slotTyped a.1.1 := by
  let u := v ∘ (slotPath i).bank
  have A : At (slot i) v (decode.symm (slotTyped a.1.1)).val := fun j => H (.fst j)
  have eq := (read_of_at (at_slotBank v i)).symm.trans (read_of_at A)
  have h : canonical p (raw u) := eq ▸ (decode.symm (slotTyped a.1.1)).property
  refine ⟨h, ?_⟩
  exact (congrArg decode (Subtype.ext eq)).trans (decode.apply_symm_apply _)

private theorem bankLast : (slotPath (p:=p) (k:=k) i).bank (Fin.last _) = Fin.last _ := by
  exact @Fin.lastCases_last (Sh p).size (fun _ => Fin ((ShapeOf p m k).size+1)) _ (fun j => ((finProdFinEquiv (i,j.castAdd _)).castAdd _).castSucc)

include hb in
theorem slotAt_of_cell (a : ECArithNet.Checked E seed T k b) (H : At (cell i) v (slotData a))
    (hz : v (Fin.last _) = false) : (slotAt E seed T i).OK v := by
  let u := v ∘ (slotPath i).bank
  obtain ⟨h,ht⟩ := slotView v i a H
  have eq : (⟨i.val/4,by omega⟩ : Fin m) = b := Fin.ext hb
  unfold slotAt; rw [eq]; apply (slotBlock_iff E seed b T _ v (hash_route i v)).mpr
  refine ⟨?_, h, ?_, ?_⟩
  · exact (congrArg v (bankLast i)).trans hz
  · rw [neg_value u h,parity_value u h,ht]; rfl
  · have sem := ECAddress.slot_semantics E seed T b a.1.1
    have hn := sem.2.2.1
    have diff : diffCert (slotPath i) v = a.1.1.1.2.2 := by
      apply Prod.ext
      · apply Eq.trans _ ((numBits _).apply_symm_apply _)
        apply congrArg (numBits _); exact funext fun j => H (.snd (.fst (.word j)))
      · exact funext fun j => H (.snd (.snd (.fst (.word j))))
    rw [ht,diff]; exact (show (false, (slotTyped a.1.1).1.2) = a.1.1.1.1 from Prod.ext hn.symm rfl) ▸ sem

theorem bankRow_of_cell (a : ECArithNet.Checked E seed T k b) (H : At (cell i) v (slotData a)) :
    let I := inputs (p:=p) (m:=m) (k:=k)
    ECAddrGadget.good T ((I.parity i).eval v) (fun j => (I.hash i j).eval v)
      (fun j => (I.selected i j).eval v, fun j => (Ref.reg (I.addr i j)).eval v, fun j => (I.carry i j).eval v) := by
  let u := v ∘ (slotPath i).bank
  obtain ⟨h,ht⟩ := slotView v i a H
  let I := inputs (p:=p) (m:=m) (k:=k)
  have par : (I.parity i).eval v = ECAddrGadget.odd a.1.1 := by
    have hr := (congrArg v (bankName_index (k:=k) i (CurveRows.ybit ⟨0,hd p⟩)).symm).trans (parity_value u h)
    rw [ht] at hr; exact hr
  have hh : (fun j => (I.hash i j).eval v) = ECAddrGadget.digits (busWidth p k) (ECAddrGadget.hash a.1.1) := by
    funext j; have eq := RangeRows.pad_eval (n:=busWidth p k) (slotPath i).hash v (rawHash u) (hash_route i v) j
    change _ = (((slotTyped a.1.1).2.1 6).1.val.testBit j.val)
    rw [← ht, outVal]; exact eq
  have s (n : Fin 3) (j : Fin (busWidth p k)) := H (.snd (.snd (.snd (.vec n (.word j)))))
  have e1 : (fun j => (I.selected i j).eval v) = a.1.2.1 := funext (s 0)
  have e2 : (fun j => (Ref.reg (I.addr i j)).eval v) = a.1.2.2.1 := funext (s 1)
  have e3 : (fun j => (I.carry i j).eval v) = a.1.2.2.2 := funext (s 2)
  dsimp only; rw [par,hh,e1,e2,e3]; exact a.2

section Chain
variable {s : Shape} {n : ℕ}
noncomputable def ptData (q : Coords p) : (PointCell (width p)).Data :=
  let a := PointEqv.symm q
  (a.1, a.2.1.val, a.2.2.val)
private theorem ptData_inj : Function.Injective (ptData (p:=p)) := by
  intro a b he; apply PointEqv.symm.injective
  have h1 := congrArg (fun x : (PointCell (width p)).Data => x.1) he
  have h2 := congrArg (fun x : (PointCell (width p)).Data => x.2.1) he
  have h3 := congrArg (fun x : (PointCell (width p)).Data => x.2.2) he
  exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Subtype.ext h3))
private theorem point_round (a : Bool × ECAddRows.Bd p × ECAddRows.Bd p) :
    ptData (PointEqv a) = (a.1, a.2.1.val, a.2.2.val) := by
  unfold ptData; rw [Equiv.symm_apply_apply]; rfl

def showsPoint (w : Wires s) (v : Bits (s.size+1)) (q : Coords p) :=
  w.1.eval v = q.1 ∧ evalWord w.2.1 v q.2.1.val ∧ evalWord w.2.2 v q.2.2.val
private theorem shows_of_at (f : Path (PointCell (width p)) s) (v : Bits (s.size+1)) (q : Coords p)
    (h : At f v (ptData q)) : showsPoint (pointWires f) v q := by
  let a := PointEqv.symm q
  have eq : PointEqv a = q := PointEqv.apply_symm_apply _
  rw [← eq,point_round] at h; rw [← eq]
  refine ⟨h (.fst .bit), ?_, ?_⟩
  · change evalWord _ _ (Z a.2.1).val; rw [resVal]; exact wordAt (fun j => h (.snd (.fst (.fst j))))
  · change evalWord _ _ (Z a.2.2).val; rw [resVal]; exact wordAt (fun j => h (.snd (.snd (.fst j))))

variable (hp : 3 < p) (pts : Fin (n+1) → Point E)
noncomputable abbrev sw := S8K.SWEquiv.equiv E (S8K.SWEquiv.six_ne_zero hp)
noncomputable def totalAt (j : Fin (n+1)) := pts 0 + Fin.partialSum (fun k : Fin n => pts k.succ) j
private theorem totalAt_zero : totalAt pts 0 = pts 0 := by simp [totalAt]
private theorem totalAt_succ (j : Fin n) : totalAt pts j.succ = totalAt pts j.castSucc + pts j.succ := by
  simp only [totalAt, Fin.partialSum_succ, add_assoc]
noncomputable def mData (j : Fin (n+1)) := sliceData (mapCell E hp (pts j))
noncomputable def aData (j : Fin n) := ECAddRows.sliceData (coords (sw (E:=E) hp (totalAt pts j.castSucc))).1
  (coords (sw (E:=E) hp (pts j.succ))).1 (addCell E (sw (E:=E) hp (totalAt pts j.castSucc)) (sw (E:=E) hp (pts j.succ)))
noncomputable def chainData : (Chain p n).Data := (mData hp pts, aData hp pts)
private theorem mapPt (j : Fin (n+1)) : (mData hp pts j).1 = ptData (coords (sw (E:=E) hp (pts j))) := by
  rw [← mapCell_output E hp]; exact (point_round _).symm
private theorem addPt (j : Fin n) : (aData hp pts j).1 = ptData (coords (sw (E:=E) hp (totalAt pts j.succ))) := by
  rw [totalAt_succ,map_add,← addCell_output E]; exact (point_round _).symm

variable (f : Path (Chain p n) s) (input : Fin (n+1) → Wires s) (term : Path (PointCell (width p)) s) (x : Bits (s.size+1))
variable (I : ∀ j, showsPoint (input j) x (coords (pts j)))
include I in
private theorem map_iff (j : Fin (n+1)) : (mapAt E f input j).OK x ↔ At (mapPath f j) x (mData hp pts j) :=
  mapBlock_at E hp (pts j) _ x _ _ _ (I j).1 (I j).2.1 (I j).2.2
private theorem add_iff (j : Fin n) (ha : At (acc f j.castSucc) x (ptData (coords (sw hp (totalAt pts j.castSucc)))))
    (hm : At (mapPath f j.succ) x (mData hp pts j.succ)) : (addAt E f j).OK x ↔ At (addPath f j) x (aData hp pts j) := by
  have A := shows_of_at _ _ _ ha
  have H : At (fstP (mapPath f j.succ)) x (mData hp pts j.succ).1 := fun a => hm (.fst a)
  rw [mapPt] at H
  have B := shows_of_at _ _ _ H
  let l := pointWires (acc f j.castSucc)
  let r := pointWires (fstP (mapPath f j.succ))
  unfold addAt aData
  exact addBlock_at E (sw hp (totalAt pts j.castSucc)) (sw hp (pts j.succ)) (addPath f j) x l.1 r.1 l.2.1 l.2.2 r.2.1 r.2.2 A.1 B.1 A.2.1 A.2.2 B.2.1 B.2.2

include I in
theorem chain_iff : (chainBlock E f input term).OK x ↔ At f x (chainData hp pts) ∧
    At term x (ptData (coords (sw hp (totalAt pts (Fin.last n))))) := by
  rw [chainBlock_iff]
  have base (hm : At (mapPath f 0) x (mData hp pts 0)) : At (acc f 0) x (ptData (coords (sw hp (totalAt pts 0)))) := by
    rw [totalAt_zero, ← mapPt hp pts 0]; exact fun a => hm (.fst a)
  have step (j : Fin n) (h : At (addPath f j) x (aData hp pts j)) : At (acc f j.succ) x (ptData (coords (sw hp (totalAt pts j.succ)))) := by
    rw [← addPt hp pts j]; exact fun a => h (.fst a)
  constructor
  · rintro ⟨M,A,G⟩
    have hm j := (map_iff hp pts f input x I j).mp (M j)
    have ac (j : Fin (n+1)) : At (acc f j) x (ptData (coords (sw hp (totalAt pts j)))) := by
      induction j using Fin.induction with
      | zero => exact base (hm 0)
      | succ j ih => exact step j ((add_iff hp pts f x j ih (hm j.succ)).mp (A j))
    have ha j := (add_iff hp pts f x j (ac j.castSucc) (hm j.succ)).mp (A j)
    refine ⟨?_, ?_⟩
    · intro a; cases a with
      | fst a => cases a with | vec i a => exact hm i a
      | snd a => cases a with | vec i a => exact ha i a
    · have eq := (pointEq_iff ..).mp G
      rw [← read_of_at (ac (Fin.last n)),eq]; exact at_read _ _
  · rintro ⟨H,Ht⟩
    have hm (j : Fin (n+1)) : At (mapPath f j) x (mData hp pts j) := fun a => H (.fst (.vec j a))
    have ha (j : Fin n) : At (addPath f j) x (aData hp pts j) := fun a => H (.snd (.vec j a))
    have ac (j : Fin (n+1)) : At (acc f j) x (ptData (coords (sw hp (totalAt pts j)))) :=
      Fin.cases (base (hm 0)) (fun j => step j (ha j)) j
    exact ⟨fun j => (map_iff hp pts f input x I j).mpr (hm j), fun j => (add_iff hp pts f x j (ac j.castSucc) (hm j.succ)).mpr (ha j),
      (pointEq_iff ..).mpr ((read_of_at (ac (Fin.last n))).trans (read_of_at Ht).symm)⟩
end Chain

section Network
variable (E) (seed) (T) (P : Point E) (pre : List Bool)
variable (F : Fin m → List (Point E)) (hT : T ≤ p) (hk : 2*T ≤ 2^k) (hF : ListsOK E F seed T)

noncomputable abbrev decodeT := ECArithNet.tableDecode E F seed T k w3_m5_modmul_r2 hT hk hF
variable (hp : 3 < p)
noncomputable def seqPts (t : Tuples E F) (s : Bool) : Fin (2*m+1) → Point E :=
  Fin.cases (if s then 0 else P) fun q => let a := (pairIx (m:=m)).symm q
    (F a.1).get ((if s then t.2 else t.1) a.1 a.2)
private theorem seq_end (t : Tuples E F) (s : Bool) : totalAt (seqPts E P F t s) (Fin.last _) =
    (if s then 0 else P) + (base E F).tupleVal (if s then t.2 else t.1) := by
  let z := fun q : Fin (2*m) => (F ((pairIx (m:=m)).symm q).1).get ((if s then t.2 else t.1) ((pairIx (m:=m)).symm q).1 ((pairIx (m:=m)).symm q).2)
  change (if s then 0 else P) + Fin.partialSum z (Fin.last _) = _
  congr 1
  simp only [Fin.partialSum, Fin.val_last, List.take_of_length_le (List.length_ofFn.le), List.sum_ofFn]
  rw [← Equiv.sum_comp pairIx z, Fintype.sum_prod_type]; simp only [Fin.sum_univ_two]
  have zz (b : Fin m) (j : Fin 2) : z (pairIx (b,j)) = (F b).get ((if s then t.2 else t.1) b j) :=
    congrArg (fun a : Fin m × Fin 2 => (F a.1).get ((if s then t.2 else t.1) a.1 a.2)) (pairIx.symm_apply_apply (b,j))
  simp only [zz]; rfl

private theorem slotData_inj {b : Fin m} : Function.Injective (slotData (E:=E) (seed:=seed) (T:=T) (k:=k) (b:=b)) := by
  intro a c e
  have h := congrArg (fun x : (SlotCell p k).Data => x.1) e
  have typedEq := decode.symm.injective (Subtype.ext h)
  have txy := congrArg (fun x => x.1.2) typedEq
  have tr := congrArg Prod.snd typedEq
  have dif := congrArg (fun x : (SlotCell p k).Data => x.2.1) e
  have cr := congrArg (fun x : (SlotCell p k).Data => x.2.2.1) e
  have bus (n : Fin 3) := congrArg (fun x : (SlotCell p k).Data => x.2.2.2 n) e
  have af := (ECAddress.slot_semantics E seed T b a.1.1).2.2.1
  have cf := (ECAddress.slot_semantics E seed T b c.1.1).2.2.1
  apply Subtype.ext; apply Prod.ext
  · apply Subtype.ext; exact Prod.ext (Prod.ext (af.trans cf.symm) txy) (Prod.ext tr (Prod.ext ((numBits _).symm.injective dif) cr))
  · exact Prod.ext (bus 0) (Prod.ext (bus 1) (bus 2))

noncomputable def dataOf (t : Tuples E F) : (ShapeOf p m k).Data :=
  let a := (decodeT E seed T F hT hk hF).symm t
  (fun i => let u := (sideIx (m:=m)).symm i; let z := (pairIx (m:=m)).symm u.1; slotData (a z.1 z.2 u.2),
   fun j => chainData hp (seqPts E P F t (decide (j.val=1))), ptData (coords (sw hp ((base E F).tupleVal t.2))))
private theorem data_slot (t : Tuples E F) (b : Fin m) (j : Fin 2) (s : Bool) :
    (dataOf E seed T P F hT hk hF hp t).1 (ix s (pointIdx b j)) = slotData (((decodeT E seed T F hT hk hF).symm t) b j s) := by
  let a := (decodeT E seed T F hT hk hF).symm t
  let g := fun (x : Fin m × Fin 2) (s : Bool) => slotData (a x.1 x.2 s)
  let u := fun (y : Fin (2*m) × Bool) => g ((pairIx (m:=m)).symm y.1) y.2
  change u ((sideIx (m:=m)).symm (sideIx (pairIx (b,j),s))) = g (b,j) s
  rw [Equiv.symm_apply_apply]; change g ((pairIx (m:=m)).symm (pairIx (b,j))) s = g (b,j) s
  rw [Equiv.symm_apply_apply]
private theorem data_chain (t : Tuples E F) (s : Bool) :
    (dataOf E seed T P F hT hk hF hp t).2.1 (sideIdx s) = chainData hp (seqPts E P F t s) := by cases s <;> rfl
variable (a : ECArithNet.CheckedTable E seed T k)
private abbrev SlotViews (v : Bits ((ShapeOf p m k).size+1)) :=
  ∀ b j s, At (cell (ix s (pointIdx b j))) v (slotData (a b j s))
private theorem factor_view (H : SlotViews E seed T a v) (b : Fin m) (j : Fin 2) (s : Bool) :
    showsPoint (factorWires s (pointIdx b j)) v (a b j s).1.1.1.1 := by
  let w := a b j s
  let i := ix s (pointIdx b j)
  let u := v ∘ (slotPath i).bank
  obtain ⟨h,ht⟩ := slotView v i w (H b j s)
  have A := at_slotBank v i
  have xv := wordAt (f:=fun n => slot i (RangeRows.xa (.fst n))) (u:=(raw u).1.2.1.1) (fun n => A (RangeRows.xa (.fst n)))
  have yv := wordAt (f:=fun n => slot i (RangeRows.ya (.fst n))) (u:=(raw u).1.2.2.1) (fun n => A (RangeRows.ya (.fst n)))
  rw [← coordX u h, ht] at xv; rw [← coordY u h, ht] at yv
  exact ⟨(ECAddress.slot_semantics E seed T b w.1.1).2.2.1.symm,xv,yv⟩
private theorem input_view (H : SlotViews E seed T a v) (s : Bool) (l : Fin (2*m+1)) :
    showsPoint (chainIn E P s l) v (coords (seqPts E P F (decodeT E seed T F hT hk hF a) s l)) := by
  induction l using Fin.cases with
  | zero => exact ⟨rfl,fun _ => rfl,fun _ => rfl⟩
  | succ l =>
    obtain ⟨⟨b,j⟩,rfl⟩ := (pairIx (m:=m)).surjective l
    let w := a b j s
    have cg := ECAddress.coords_get E seed T b F w3_m5_modmul_r2 hT hF w.1.1
    have ev := factor_view E seed T v a H b j s
    let t := decodeT E seed T F hT hk hF a
    let D := fun z : Fin m × Fin 2 => (F z.1).get ((if s then t.2 else t.1) z.1 z.2)
    change showsPoint (factorWires s (pointIdx b j)) v (coords (D ((pairIx (m:=m)).symm (pairIx (b,j)))))
    rw [Equiv.symm_apply_apply]; rw [← cg] at ev
    cases s <;> exact ev
private theorem pre_view (H : SlotViews E seed T a v) :
    pre <+: (refs (p:=p) (m:=m) (k:=k)).map (fun r => r.eval v) ↔ prefixOK E F pre (decodeT E seed T F hT hk hF a) := by
  apply (ECArithNet.prefix_iff ..).symm.trans
  apply ECPrefix.prefix_correct E F seed T w3_m5_modmul_r2 hT hF _ _ _ (ECArithNet.forgetTable E seed T k hT hk a)
  · intro s b j l; exact (factor_view E seed T v a H b j s).2.1 l.val
  · intro s b j l; exact (factor_view E seed T v a H b j s).2.2 l.val

private theorem side_spec (H : SlotViews E seed T a v) (s : Bool) :
    let t := decodeT E seed T F hT hk hF a
    (sideBlock E P s).OK v ↔ At (chainPath s) v (chainData hp (seqPts E P F t s)) ∧
      At terminal v (ptData (coords (sw hp ((if s then 0 else P) + (base E F).tupleVal (if s then t.2 else t.1))))) := by
  dsimp only; rw [← seq_end]; exact chain_iff hp _ _ _ _ v (input_view E seed T v P F hT hk hF a H s)

private def flatNames (q : Shape) : {v : Bits (q.size+1) // v (Fin.last _) = false} ≃ q.Data :=
  PointGraph.dropLast.trans q.decode
private theorem flatAt {q : Shape} (u : {v : Bits (q.size+1) // v (Fin.last _) = false}) : At id u.val (flatNames q u) :=
  fun a => (Addr.correct a (u.val ∘ Fin.castSucc)).symm
private theorem fullAt (t : Tuples E F) (S : SlotViews E seed T ((decodeT E seed T F hT hk hF).symm t) v)
    (C : ∀ s, At (chainPath s) v (chainData hp (seqPts E P F t s)))
    (Z : At terminal v (ptData (coords (sw hp ((base E F).tupleVal t.2))))) : At id v (dataOf E seed T P F hT hk hF hp t) := by
  let d := dataOf E seed T P F hT hk hF hp t
  have sl : ∀ i, At (cell i) v (d.1 i) := slotsAll fun b j s => by rw [data_slot]; exact S b j s
  have ch (s : Bool) : At (chainPath s) v (d.2.1 (sideIdx s)) := by rw [data_chain]; exact C s
  have h0 : readPath (chainPath false) v = d.2.1 0 := read_of_at (ch false)
  have h1 : readPath (chainPath true) v = d.2.1 1 := read_of_at (ch true)
  have hr : readPath (id : Path (ShapeOf p m k) _) v = d := by
    apply Prod.ext (funext (fun i => read_of_at (sl i)))
    apply Prod.ext _ (read_of_at Z)
    funext j; refine Fin.cases h0 (fun j => ?_) j
    obtain rfl := Fin.eq_zero j; exact h1
  rw [← show readPath (id : Path (ShapeOf p m k) _) v = dataOf E seed T P F hT hk hF hp t from hr]; exact at_read _ _
private theorem coordsInj {W : WeierstrassCurve (ZMod p)} : Function.Injective (@coords p _ W) := by
  intro a b h; cases a <;> cases b <;> simp_all [coords]

variable (hm : 1 ≤ m)
include hm in
private theorem acceptedData (x : Accepted (k:=k) E seed T P pre) :
    let t := tuple E seed T P pre F hT hk hF x
    let v := (namedEquiv E seed T P pre x).1
    v (Fin.last _) = false ∧ At id v (dataOf E seed T P F hT hk hF hp t) ∧
    (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P := by
  let u := namedEquiv E seed T P pre x
  let a := checkedTable E seed T P pre x
  let t := decodeT E seed T F hT hk hF a
  have ar := (joinB_iff ..).mp u.2.1
  have rows := (manyB_iff ..).mp ar.1
  have S : SlotViews E seed T a u.val := fun b j s => checkedSlot_at u.val _ (owner b j s) (rows _) u.2.2.1
  have D (s : Bool) := side_spec E seed T u.val P F hT hk hF hp a S s
  have hx := (D false).mp ((joinB_iff ..).mp ar.2).1
  have hy := (D true).mp ((joinB_iff ..).mp ar.2).2
  simp only [Bool.false_eq_true,if_false,if_true,zero_add] at hx hy
  have eq := (sw hp (E:=E)).injective (coordsInj (ptData_inj ((read_of_at hy.2).symm.trans (read_of_at hx.2))))
  have h0 (i : Fin (4*m)) := ((slotBlock_iff E seed _ T _ u.val (hash_route i u.val)).mp (rows i)).1
  have hz (i : Fin (4*m)) : u.val (Fin.last _) = false := (congrArg u.val (bankLast i).symm).trans (h0 i)
  refine ⟨hz ⟨0,by omega⟩, fullAt E seed T u.val P F hT hk hF hp t ?_ ?_ hy.2, eq.trans (add_comm ..)⟩
  · simpa only [t,Equiv.symm_apply_apply] using S
  · intro s; cases s with
    | false => exact hx.1
    | true => exact hy.1
abbrev Target := {t : Tuples E F // (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P ∧ prefixOK E F pre t}
noncomputable def encode (hp : 3 < p) (t : Target E P pre F) : Accepted (k:=k) E seed T P pre := by
  let D := decodeT E seed T F hT hk hF
  let a := D.symm t.val
  let d := dataOf E seed T P F hT hk hF hp t.val
  let y := (flatNames _).symm d
  let x := y.val
  have atD : At id x d := (flatNames _).apply_symm_apply d ▸ flatAt y
  have S : SlotViews E seed T a x := by
    intro b j s
    rw [← data_slot E seed T P F hT hk hF hp t.val b j s]
    exact fun n => atD (.fst (.vec _ n))
  have C (s : Bool) : At (chainPath s) x (chainData hp (seqPts E P F t.val s)) := by
    rw [← data_chain E seed T P F hT hk hF hp t.val s]; exact fun n => atD (.snd (.fst (.vec _ n)))
  have Z : At terminal x (ptData (coords (sw hp ((base E F).tupleVal t.val.2)))) := fun n => atD (.snd (.snd n))
  have DA : decodeT E seed T F hT hk hF a = t.val := D.apply_symm_apply _
  have side (s : Bool) : (sideBlock E P s).OK x := by
    apply (side_spec E seed T x P F hT hk hF hp a S s).mpr
    rw [DA]; refine ⟨C s, ?_⟩
    cases s with
    | true => simpa only [if_true, zero_add] using Z
    | false => simpa only [Bool.false_eq_true, if_false, t.property.1, add_comm P] using Z
  refine (namedEquiv (k:=k) E seed T P pre).symm ?_
  refine ⟨x,(joinB_iff ..).mpr ⟨(manyB_iff ..).mpr ?_,(joinB_iff ..).mpr ⟨side false,side true⟩⟩,(ECArithNet.bank_iff ..).mpr ?_,?_⟩
  · exact slotsAll fun b j s => slotAt_of_cell x _ (owner b j s) (a b j s) (S b j s) y.2
  · exact slotsAll fun b j s => bankRow_of_cell x _ (a b j s) (S b j s)
  · apply (pre_view E seed T x pre F hT hk hF a S).mpr; rw [DA]; exact t.property.2

private theorem encode_named (t : Target E P pre F) : (namedEquiv E seed T P pre (encode E seed T P pre F hT hk hF hp t)).val =
    ((flatNames _).symm (dataOf E seed T P F hT hk hF hp t.val)).val :=
  congrArg Subtype.val ((namedEquiv E seed T P pre).apply_symm_apply _)

private theorem tuple_encode (t : Target E P pre F) : tuple E seed T P pre F hT hk hF (encode E seed T P pre F hT hk hF hp t) = t.val := by
  let u := encode E seed T P pre F hT hk hF hp t
  let y := namedEquiv E seed T P pre u
  let D := decodeT E seed T F hT hk hF
  let a := checkedTable E seed T P pre u
  have A : At id y.val (dataOf E seed T P F hT hk hF hp t.val) := by
    rw [show y.val = _ from encode_named E seed T P pre F hT hk hF hp t]
    let d := dataOf E seed T P F hT hk hF hp t.val
    let q := flatNames (ShapeOf p m k)
    have hh : At id (q.symm d).val (q (q.symm d)) := flatAt (q.symm d)
    rw [Equiv.apply_symm_apply] at hh; exact hh
  have B : a = D.symm t.val := by
    funext b j s; apply slotData_inj E seed T
    have rows := (manyB_iff ..).mp ((joinB_iff ..).mp y.2.1).1
    have hs : At (cell (ix s (pointIdx b j))) y.val (slotData (a b j s)) := checkedSlot_at y.val _ (owner b j s) (rows _) y.2.2.1
    have ht : At (cell (ix s (pointIdx b j))) y.val ((dataOf E seed T P F hT hk hF hp t.val).1 (ix s (pointIdx b j))) := fun n => A (.fst (.vec _ n))
    exact (read_of_at hs).symm.trans ((read_of_at ht).trans (data_slot E seed T P F hT hk hF hp _ _ _ _))
  exact (congrArg D B).trans (D.apply_symm_apply _)

/-- Physical acceptance has exactly one assignment per endpoint- and prefix-correct tuple. -/
noncomputable def acceptEquiv (hp : 3 < p) (hm : 1 ≤ m) : Accepted (k:=k) E seed T P pre ≃ Target E P pre F where
  toFun x := ⟨tuple E seed T P pre F hT hk hF x, (acceptedData E seed T P pre F hT hk hF hp hm x).2.2,
    accepted_prefix E seed T P pre F hT hk hF x⟩
  invFun := encode E seed T P pre F hT hk hF hp
  left_inv x := by
    let y := namedEquiv E seed T P pre x
    have H := acceptedData E seed T P pre F hT hk hF hp hm x
    let y0 : {v : Bits ((ShapeOf p m k).size+1) // v (Fin.last _) = false} := ⟨y.val,H.1⟩
    have he := (read_of_at (flatAt y0)).symm.trans (read_of_at H.2.1)
    apply (namedEquiv E seed T P pre).injective; apply Subtype.ext
    exact (encode_named E seed T P pre F hT hk hF hp _).trans (congrArg Subtype.val ((flatNames _).symm_apply_eq.mpr he.symm))
  right_inv t := Subtype.ext (tuple_encode E seed T P pre F hT hk hF hp t)

@[simp] theorem acceptEquiv_tuple (x : Accepted (k:=k) E seed T P pre) :
    (acceptEquiv E seed T P pre F hT hk hF hp hm x).val = tuple E seed T P pre F hT hk hF x := rfl
/-- The joined certificate picked by either equivalence is the unique trace at
    this physical assignment's tuple, and its checked table is the physical one. -/
noncomputable def joinedWitness (hp : 3 < p) (hm : 1 ≤ m) (x : Accepted (k:=k) E seed T P pre) :=
  let t := acceptEquiv E seed T P pre F hT hk hF hp hm x
  (ECChains.joinedEndpoint E F hp P t.val t.2.1).exists.choose

theorem cert_compare (x : Accepted (k:=k) E seed T P pre) :
    let t := acceptEquiv E seed T P pre F hT hk hF hp hm x
    let c := ECArithNet.certEquiv E F seed T k hp P w3_m5_modmul_r2 hT hk hF pre
    (c.symm t).val = (checkedTable E seed T P pre x, joinedWitness E seed T P pre F hT hk hF hp hm x) := by
  dsimp only
  let t := acceptEquiv E seed T P pre F hT hk hF hp hm x
  let c := ECArithNet.certEquiv E F seed T k hp P w3_m5_modmul_r2 hT hk hF pre
  let w := joinedWitness E seed T P pre F hT hk hF hp hm x
  have hw : joinedOK E F hp P t.val w := (ECChains.joinedEndpoint E F hp P t.val t.2.1).exists.choose_spec
  let z : {a : ECArithNet.CheckedTable E seed T k × Joined E // prefixOK E F pre (decodeT E seed T F hT hk hF a.1) ∧ joinedOK E F hp P (decodeT E seed T F hT hk hF a.1) a.2} :=
    ⟨(checkedTable E seed T P pre x,w),t.2.2,hw⟩
  have he : c z = t := Subtype.ext rfl
  exact congrArg Subtype.val (c.symm_apply_eq.mpr he.symm)
end Network

end DetDLP.M3B.ECNetBijection


