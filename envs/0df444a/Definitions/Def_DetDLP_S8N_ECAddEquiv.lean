-- Prove2me | Definitions.Def_DetDLP_S8N_ECAddEquiv
-- name    : DetDLP_S8N_ECAddEquiv
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:18:34.060333+00:00
-- url     : https://prove2.me/theorems/cc4d9ea0-0a07-4413-bb36-3eac2b080287
-- title:
--   Short-Weierstrass addition register slice bijection
-- statement:
--   For points $P,Q$ on the short-Weierstrass curve over $\mathbb F_p$, there is exactly one register slice accepted by the addition block with inputs $\operatorname{coords}(P)$ and $\operatorname{coords}(Q)$. Its output flag and unsigned coordinate words agree with $\operatorname{coords}(P+Q)$. Uniqueness includes the inverse operands, both zero flags, the slope word and all fifteen hash slots; it does not require uniqueness of the enclosing register bank.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8N_ECAddRoutes
import Theorems.Thm_DetDLP_w3_m5_modmul_r2
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace DetDLP.S8N.ECAddEquiv
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout S8N.ECAddRoutes S8M.ECMapRows
noncomputable section
variable {p : ℕ} [Fact p.Prime] {s : Shape}
private abbrev Z := zmodEquiv (fits p).le
private abbrev R := runEquiv (GateSemantics.hd p) (fits p).le
abbrev Witness (p : ℕ) := AddCert p × ((GateAux p × (GateAux p × Unit) × GateAux p × (GateAux p × Unit) × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × GateAux p × Unit) × Unit)
private abbrev Cell (p : ℕ) := CheckedRun (width p) p (GateSemantics.hd p) × AuxBank (width p)
@[ext] structure Slice (p : ℕ) where
  o : Bool
  a : Fin 4 → Bounded (d := width p) p
  b : Fin 2 → Bool
  g : Fin 15 → Cell p
private abbrev out (u : Slice p) : Coords p := (u.o,Z (u.a 0),Z (u.a 1))
private abbrev runAt (u : Slice p) (k : Fin 15) : Run p := R (u.g k).1
private def gate (v : Cell p) : GateAux p := (auxEquiv _ v.2,value v.1.1.val.2.1,v.1.1.val.2.2)
private def witness (u : Slice p) : Witness p :=
  let r := runAt u; let t := fun k => gate (u.g k)
  ((r 0,(u.b 0,Z (u.a 2),r 1),r 2,(u.b 1,Z (u.a 3),r 3),r 4,r 5,r 6,r 7,r 8,r 9,r 10,r 11,r 12,r 13,r 14,()),(t 0,(t 1,()),t 2,(t 3,()),t 4,t 5,t 6,t 7,t 8,t 9,t 10,t 11,t 12,t 13,t 14,()),())
def pack (o : Coords p) (w : Witness p) : Slice p :=
  let ⟨⟨g0,(b1,a1,g1),g2,(b3,a3,g3),g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,_⟩,⟨t0,(t1,()),t2,(t3,()),t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,_⟩,_⟩ := w
  ⟨o.1,fun k => Z.symm (![o.2.1,o.2.2,a1,a3] k),![b1,b3],fun k => (R.symm (![g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14] k),(auxEquiv _).symm ((![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14] k).1))⟩
theorem unpack (u : Slice p) : pack (out u) (witness u) = u := by
  rcases u with ⟨o,a,b,g⟩; apply Slice.ext <;> first | rfl | (funext k; fin_cases k <;> simp [pack,witness,gate,runAt])
private theorem gate_restore (r : Run p) (t : GateAux p) (h : w3_slotLt _ r.1.val p t.2) : gate (R.symm r,(auxEquiv _).symm t.1) = t := by
  refine Prod.ext ((auxEquiv _).apply_symm_apply _) ?_; let v := R.symm r
  have hv : (Z v.1).val = r.1.val := congrArg (fun z : Run p => z.1.val) (R.apply_symm_apply r)
  rw [GateSemantics.resVal] at hv; obtain ⟨_,_,uniq⟩ := (w3_slotLt_spec (r.1.val_lt.trans (fits p)) (fits p).le).2 r.1.val_lt
  exact (uniq _ (hv ▸ (below_iff p v.1.val).1 v.1.property)).trans (uniq _ h).symm
theorem repack (E : WeierstrassCurve (ZMod p)) (P Q o : Coords p) (w : Witness p) (h : (addChecks E P Q o w.1).bits w.2) :
    out (pack o w) = o ∧ witness (pack o w) = w := by
  rcases w with ⟨⟨g0,⟨b1,a1,g1⟩,g2,⟨b3,a3,g3⟩,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,⟨⟩⟩,⟨t0,⟨t1,⟨⟩⟩,t2,⟨t3,⟨⟩⟩,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,⟨⟩⟩,⟨⟩⟩
  have H0 := gate_restore g0 t0 h.1.1.2; have H1 := gate_restore g1 t1 h.1.2.1.1.2; have H2 := gate_restore g2 t2 h.1.2.2.1.2; have H3 := gate_restore g3 t3 h.1.2.2.2.1.1.2; have H4 := gate_restore g4 t4 h.1.2.2.2.2.1.2; have H5 := gate_restore g5 t5 h.1.2.2.2.2.2.1.2; have H6 := gate_restore g6 t6 h.1.2.2.2.2.2.2.1.2; have H7 := gate_restore g7 t7 h.1.2.2.2.2.2.2.2.1.2; have H8 := gate_restore g8 t8 h.1.2.2.2.2.2.2.2.2.1.2; have H9 := gate_restore g9 t9 h.1.2.2.2.2.2.2.2.2.2.1.2; have H10 := gate_restore g10 t10 h.1.2.2.2.2.2.2.2.2.2.2.1.2; have H11 := gate_restore g11 t11 h.1.2.2.2.2.2.2.2.2.2.2.2.1.2; have H12 := gate_restore g12 t12 h.1.2.2.2.2.2.2.2.2.2.2.2.2.1.2; have H13 := gate_restore g13 t13 h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2; have H14 := gate_restore g14 t14 h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2
  simp [pack,out,witness,runAt,H0,H1,H2,H3,H4,H5,H6,H7,H8,H9,H10,H11,H12,H13,H14]
private def chooseSlope {α : Type} (i j bx by' : Bool) (ch tan zero : α) : α :=
  if !i && !j && !bx then ch else if !i && !j && bx && !by' then tan else zero
private abbrev slopeVal (P Q : Coords p) (u : Slice p) := chooseSlope P.1 Q.1 (u.b 0) (u.b 1) (runAt u 5).1 (runAt u 8).1 0
private abbrev S (p : ℕ) := addShape (width p) (GateSemantics.e p)
private def data (u : Slice p) (l : Bits (width p)) : (S p).Data := ((u.o,fun k => (u.a k).val),(u.b,l),fun k => (rawRun (u.g k).1,(u.g k).2))
private abbrev bits (x : ZMod p) : Bits (width p) := ((Z.symm x).val).1
private theorem bits_val (x : ZMod p) : (value (bits x)).val = x.val := by rw [← GateSemantics.resVal _ (Z.symm x).property,Equiv.apply_symm_apply]
private theorem slope_bit (i j b c : Bool) (x y : ZMod p) (k : ℕ) :
    mux i j b c (x.val.testBit k) (y.val.testBit k) = (chooseSlope i j b c x y 0).val.testBit k := by
  unfold mux chooseSlope; split <;> first | rfl | split <;> simp
private def dst (P Q : Coords p) (b c : Bool) (x y : ZMod p) : Coords p :=
  if P.1 then Q else if Q.1 then (false,P.2) else if b && c then (true,0,0) else (false,x,y)
private theorem dst_bits (P Q : Coords p) (b c : Bool) (x y : ZMod p) : let D := dst P Q b c x y
    D.1 = (if P.1 then Q.1 else !Q.1 && b && c) ∧
    (∀ k, D.2.1.val.testBit k = dest P.1 Q.1 b c (P.2.1.val.testBit k) (Q.2.1.val.testBit k) (x.val.testBit k)) ∧
    (∀ k, D.2.2.val.testBit k = dest P.1 Q.1 b c (P.2.2.val.testBit k) (Q.2.2.val.testBit k) (y.val.testBit k)) := by
  rcases P with ⟨i,_⟩; rcases Q with ⟨j,_⟩; cases i <;> cases j <;> cases b <;> cases c <;> simp [dst,dest]
private abbrev block (E : WeierstrassCurve (ZMod p)) := @addBlock (width p) (GateSemantics.e p) s (GateSemantics.hd p) p (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val
private theorem rows_iff (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (u : Slice p) (l : Bits (width p)) (f : Path (S p) s) (v : Bits (s.size+1))
    (i j : Ref s) (x y X Y : Word s) (H : At f v (data u l)) (I : i.eval v = P.1) (J : j.eval v = Q.1)
    (hx : evalWord x v P.2.1.val) (hy : evalWord y v P.2.2.val) (hX : evalWord X v Q.2.1.val) (hY : evalWord Y v Q.2.2.val) :
    (block E i x y j X Y f).OK v ↔ l = bits (slopeVal P Q u) ∧ (addChecks E P Q (out u) (witness u).1).bits (witness u).2 := by
  let z := fun k => (runAt u k).1; let a := fun k => Z (u.a k); let L := slopeVal P Q u
  have one : (1 : ZMod p).val = 1 := by have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩; exact ZMod.val_one _
  have valA (k) : (value (u.a k).val.1).val = (a k).val := (GateSemantics.resVal _ _).symm
  have ltA (v : Bounded (d:=width p) p) := (below_iff p v.val).1 v.property
  have ltG (k) : w3_slotLt _ (z k).val p (gate (u.g k)).2 := by change w3_slotLt _ (Z _).val _ _; rw [GateSemantics.resVal]; exact ltA _
  let eqw (a b : ZMod p) := ∀ k : Fin (width p), a.val.testBit k = b.val.testBit k
  let inv (b : Bool) (x y r : ZMod p) := if b then eqw x 0 ∧ eqw y 0 else eqw r 1
  have invEq (b : Bool) (x y r : ZMod p) : (∀ k : Fin (width p), if b then x.val.testBit k = false ∧ y.val.testBit k = false else r.val.testBit k = (1 : ℕ).testBit k) ↔ inv b x y r := by cases b <;> simp [inv,eqw,one,forall_and]
  let D := dst P Q (u.b 0) (u.b 1) (z 11) (z 14); have dd := dst_bits P Q (u.b 0) (u.b 1) (z 11) (z 14)
  have slEq : (∀ k : Fin (width p), (value l).val.testBit k = L.val.testBit k) ↔ l = bits L := by
    simp only [← bits_val L,value_bit,funext_iff]
  refine (rows_iff_decoded (-1 : ZMod p).val (3 : ZMod p).val (-27*E.c₄).val i j x y X Y _ _ _ _ f v u.o _ u.b l (fun k => (u.g k).1) _ H hx hy hX hY).trans ?_; dsimp only
  simp only [ltA,implies_true,and_self,true_and]; simp only [valA,I,J,invEq]
  let g := ECAddRoutes.args (-1 : ZMod p).val 1 (3 : ZMod p).val (-27*E.c₄).val 0 P.2.1.val P.2.2.val Q.2.1.val Q.2.2.val (value l).val (fun k => (a k).val) (fun k => (z k).val)
  let ht (k : Fin 15) := w3_slotHashBits (GateSemantics.hd p) (g k).1 (g k).2.2 (g k).2.1 (z k).val (runAt u k).2 (gate (u.g k)).1
  change ((∀ k, ht k) ∧ inv (u.b 0) (z 0) (a 2) (z 1) ∧ inv (u.b 1) (z 2) (a 3) (z 3) ∧
    (∀ k : Fin (width p), (value l).val.testBit k = mux P.1 Q.1 (u.b 0) (u.b 1) ((z 5).val.testBit k) ((z 8).val.testBit k)) ∧ _) ↔ l = bits L ∧ _
  simp only [slope_bit,← dd.1]; change ((∀ k, ht k) ∧ _ ∧ _ ∧ (∀ k : Fin (width p), (value l).val.testBit k = L.val.testBit k) ∧ u.o = D.1 ∧ (∀ k : Fin (width p), (a 0).val.testBit k = dest P.1 Q.1 (u.b 0) (u.b 1) _ _ ((z 11).val.testBit k)) ∧ (∀ k : Fin (width p), (a 1).val.testBit k = dest P.1 Q.1 (u.b 0) (u.b 1) _ _ ((z 14).val.testBit k))) ↔ _
  rw [slEq]; simp only [← dd.2.1,← dd.2.2]
  by_cases hl : l = bits L
  · let test (k : Fin 15) (a x b : ZMod p) := w3_slotHashBits (GateSemantics.hd p) a.val b.val x.val (z k).val (runAt u k).2 (gate (u.g k)).1
    let lt (k : Fin 15) := w3_slotLt _ (z k).val p (gate (u.g k)).2
    change _ ↔ l = bits L ∧ (((test 0 (-1) P.2.1 Q.2.1 ∧ lt 0) ∧ ((test 1 (z 0) (a 2) 0 ∧ lt 1) ∧ inv (u.b 0) (z 0) (a 2) (z 1)) ∧ (test 2 1 P.2.2 Q.2.2 ∧ lt 2) ∧ ((test 3 (z 2) (a 3) 0 ∧ lt 3) ∧ inv (u.b 1) (z 2) (a 3) (z 3)) ∧ (test 4 (-1) P.2.2 Q.2.2 ∧ lt 4) ∧ (test 5 (z 4) (a 2) 0 ∧ lt 5) ∧ (test 6 P.2.1 P.2.1 0 ∧ lt 6) ∧ (test 7 3 (z 6) (-27*E.c₄) ∧ lt 7) ∧ (test 8 (z 7) (a 3) 0 ∧ lt 8) ∧ (test 9 L L 0 ∧ lt 9) ∧ (test 10 (-1) P.2.1 (z 9) ∧ lt 10) ∧ (test 11 (-1) Q.2.1 (z 10) ∧ lt 11) ∧ (test 12 (-1) (z 11) P.2.1 ∧ lt 12) ∧ (test 13 L (z 12) 0 ∧ lt 13) ∧ (test 14 (-1) P.2.2 (z 13) ∧ lt 14) ∧ True) ∧ u.o = D.1 ∧ eqw (a 0) D.2.1 ∧ eqw (a 1) D.2.2)
    simp only [hl,eq_self,true_and,and_true,show ∀ k, lt k from ltG,Fin.forall_fin_succ,Fin.forall_fin_zero,ht,g,ECAddRoutes.args,Matrix.cons_val_zero,Matrix.cons_val_succ,bits_val,test,ZMod.val_zero,one,eqw]
    tauto
  · simp [hl]
/-- Realizability in any enclosing bank, with the two coordinate triples fixed. -/
def Accepted (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (w : (S p).Data) : Prop :=
  ∃ (s : Shape) (f : Path (S p) s) (v : Bits (s.size+1)) (i j : Ref s) (x y X Y : Word s), At f v w ∧
    i.eval v = P.1 ∧ j.eval v = Q.1 ∧ evalWord x v P.2.1.val ∧ evalWord y v P.2.2.val ∧ evalWord X v Q.2.1.val ∧ evalWord Y v Q.2.2.val ∧ (block E i x y j X Y f).OK v
private theorem decodeAccepted (E : WeierstrassCurve (ZMod p)) (P Q : Coords p) (w : (S p).Data) (hw : Accepted E P Q w) :
    ∃ u : Slice p, data u (bits (slopeVal P Q u)) = w ∧ (addChecks E P Q (out u) (witness u).1).bits (witness u).2 := by
  obtain ⟨s,f,v,i,j,x,y,X,Y,H,I,J,hx,hy,hX,hY,ok⟩ := hw
  have hr := ((joinB_iff _ _ _).1 ok); have A := (many_iff _ _ _).1 hr.1; have G := (many_iff _ _ _).1 ((joinB_iff _ _ _).1 hr.2).1
  have bound {k : Path (triple (width p)) s} {a : Triple (width p)} (h : At k v a) := (checker_iff p k v a h).1
  let r (k : Fin 15) := (w.2.2 k).1
  let u : Slice p := ⟨w.1.1,fun k => ⟨w.1.2 k,bound (fun t => H (.fst (.snd (.vec k t)))) (A k)⟩,w.2.1.1,fun k =>
    ((⟨(r k).1,bound (fun t => H (.snd (.snd (.vec k (.fst (.fst t)))))) ((joinB_iff _ _ _).1 (G k)).1⟩,
    (⟨(r k).2.1.1,bound (fun t => H (.snd (.snd (.vec k (.fst (.snd (.fst (.fst t)))))))) ((joinB_iff _ _ _).1 (G k)).2⟩,(r k).2.1.2),(r k).2.2),(w.2.2 k).2)⟩
  obtain ⟨hl,h⟩ := (rows_iff E P Q u w.2.1.2 f v i j x y X Y H I J hx hy hX hY).1 ok
  exact ⟨u,hl ▸ (rfl : data u w.2.1.2 = w),h⟩
/-- Raw output words are interpreted as naturals; no reduction modulo the field is needed. -/
def outputWords (w : (S p).Data) : Bool × ℕ × ℕ := (w.1.1,(value (w.1.2 0).1).val,(value (w.1.2 1).1).val)
def coordWords (o : Coords p) := (o.1,o.2.1.val,o.2.2.val)
/-- Uniqueness concerns the whole register slice. The final clause applies to every accepted slice. -/
theorem acceptedSlice_unique (E : WeierstrassCurve (ZMod p)) (P Q : (S8K.SWEquiv.short E).toAffine.Point) :
    (∃! w : (addShape (width p) (GateSemantics.e p)).Data, Accepted E (coords P) (coords Q) w) ∧
    ∀ w, Accepted E (coords P) (coords Q) w → outputWords w = coordWords (coords (P+Q)) := by
  let o := coords (P+Q); obtain ⟨c,hc,uc⟩ := swAdd_unique_bits E w3_m5_modmul_r2 P Q
  let u := pack o c; obtain ⟨ho,he⟩ := repack E (coords P) (coords Q) o c hc
  have hu : (addChecks E (coords P) (coords Q) (out u) (witness u).1).bits (witness u).2 := by rw [show out u = o from ho,show witness u = c from he]; exact hc
  let l := bits (slopeVal (coords P) (coords Q) u); let w := data u l
  let v : Bits ((S p).size+1) := Fin.lastCases false ((S p).decode.symm w)
  have H : At id v w := by intro j; change v j.index.castSucc = _; simp [v,← Addr.correct j ((S p).decode.symm w)]
  have ok : Accepted E (coords P) (coords Q) w := ⟨_,id,v,.pin _,.pin _,pub _,pub _,pub _,pub _,H,rfl,rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,
    (rows_iff E _ _ u l id v _ _ _ _ _ _ H rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).2 ⟨rfl,hu⟩⟩
  have unique (w' : (S p).Data) (hw : Accepted E (coords P) (coords Q) w') : w' = w := by
    obtain ⟨t,ht,h⟩ := decodeAccepted E _ _ w' hw
    have ot : out t = o := swAdd_sound E w3_m5_modmul_r2 P Q _ _ ((swAdd_lift E _ _ _ _).1 _ h)
    rw [ot] at h; have ut : t = u := by rw [← unpack t,ot,uc (witness t) h]
    exact ht.symm.trans (ut ▸ rfl)
  refine ⟨⟨w,ok,unique⟩,?_⟩; intro w' hw; rw [unique w' hw]
  change (u.o,(value (u.a 0).val.1).val,(value (u.a 1).val.1).val) = coordWords o
  rw [← GateSemantics.resVal _ (u.a 0).property,← GateSemantics.resVal _ (u.a 1).property]; exact congrArg coordWords ho
end
end DetDLP.S8N.ECAddEquiv


