-- Prove2me | Definitions.Def_DetDLP_S8M_ECMapRows
-- name    : DetDLP_S8M_ECMapRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:03:18.294945+00:00
-- url     : https://prove2.me/theorems/1b3fa96f-3bd7-4e92-8ee9-d122395b9ace
-- title:
--   Declarative register rows for EC-to-short-Weierstrass conversion
-- statement:
--   For one change of coordinates on a Weierstrass curve over $\mathbb F_p$, `mapBlock` checks four residue equations: $X=36x+3b_2$, $t=a_1x+a_3$, $u=2y+t$, and $Y=108u$. The output flag copies the input flag. At infinity the output coordinates are both zero; otherwise they are $(X,Y)$. Each residue triple carries its strict-bound witness.
--
--   `mapBlock_iff` identifies row acceptance with the bit predicate of `ECAddLayout.mapChecks`. The inverse lemmas `unpack` and `repack` recover the register slice from its decoded coordinates and certificate, and recover every valid certificate from its slice. For an elliptic curve, $p>3$, and the multiplication interface of `ecToSW_unique_bits`, `acceptedSlice_unique` proves that each input point admits exactly one accepted raw slice, independently of its placement in an enclosing register bank.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8O_ECAddLayout
import Definitions.Def_DetDLP_S8H0_GateSemantics
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.S8M.ECMapRows
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout
variable {d e : ℕ} {s : Shape}
abbrev slot (d e : ℕ) := Shape.pair (run d e) (auxShape d)
def mapShape (d e : ℕ) := Shape.pair (.pair .bit (.pair (triple d) (triple d))) (.vec 4 (slot d e))
private abbrev fstP {a b : Shape} (f : Path (.pair a b) s) : Path a s := fun j => f (.fst j)
private abbrev sndP {a b : Shape} (f : Path (.pair a b) s) : Path b s := fun j => f (.snd j)
private abbrev rwrd (f : Path (triple d) s) := word (fstP f)
private abbrev refw {n : ℕ} (f : Path (.word n) s) (i : Fin n) : Ref s := .reg (f (.word i))
private def gw (hd : 1 ≤ d) (p : ℕ) (a x b : Word s) (f : Path (slot d e) s) : Wires d hd s :=
  let r := fstP f; let k := fstP (sndP r); let l := sndP k; let m := sndP l; let t := sndP f
  ⟨a,x,b,rwrd (fstP r),rwrd (fstP k),word (fstP l),word (fstP (fstP m)),word (fstP (sndP m)), word (fstP (sndP t)),fun i => .masked (p.testBit i) (sndP (sndP r) .bit),
   pad (refw (sndP (fstP m))),pad (refw (sndP (sndP m))),refw (fstP t), refw (fstP (sndP (sndP t))),refw (sndP (sndP (sndP t)))⟩
private abbrev sp (f : Path (mapShape d e) s) (g : Fin 4) : Path (slot d e) s := fun j => f (.snd (.vec g j))
private abbrev result (f : Path (slot d e) s) := fstP (fstP f)
private abbrev remain (f : Path (slot d e) s) := fstP (fstP (sndP (fstP f)))
private def maskEq (f : Ref s) (o z : Word s) (d : ℕ) := rows d 3 (fun i => ![f,o i,z i]) (fun _ v => v 1 == (!v 0 && v 2))
private abbrev args4 (p b2 a1 a3 : ℕ) (x y : Word s) (f : Path (mapShape d e) s) : Fin 4 → Word s × Word s × Word s :=
  let z := fun i => rwrd (result (sp f i)); ![(pub (36%p),x,pub (3*b2%p)),(pub a1,x,pub a3),(pub (2%p),y,z 1),(pub (108%p),z 2,pub 0)]
private def ranges (p : ℕ) (f : Path (mapShape d e) s) :=
  let o := sndP (fstP f); joinB (joinB (checker p (fstP o)) (checker p (sndP o))) (many 3 fun i => joinB (checker p (result (sp f i))) (checker p (remain (sp f i))))
def mapBlock (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (inFlag : Ref s) (inX inY : Word s) (path : Path (mapShape d e) s) : B (s.size+1) :=
  let o := sndP (fstP path); let z := fun i => rwrd (result (sp path i))
  joinB (ranges p path) (joinB (many 3 fun i => let a := args4 p b2 a1 a3 inX inY path i
    HashRows.block p (gw hd p a.1 a.2.1 a.2.2 (sp path i))) (joinB (eqs 1 (fun _ => .reg (fstP (fstP path) .bit)) (fun _ => inFlag))
    (joinB (maskEq inFlag (rwrd (fstP o)) (z 0) d) (maskEq inFlag (rwrd (sndP o)) (z 3) d))))
variable {p : ℕ} [Fact p.Prime]
noncomputable section
private abbrev R := runEquiv (GateSemantics.hd p) (fits p).le
private abbrev Z := zmodEquiv (fits p).le
private abbrev rawRun (r : CheckedRun (width p) p (GateSemantics.hd p)) : (run (width p) (GateSemantics.e p)).Data := (r.1.val, (r.2.1.1.val,r.2.1.2),r.2.2)
def At {q : Shape} (f : Path q s) (v : Bits (s.size+1)) (u : q.Data) := ∀ j, (Ref.reg (f j)).eval v = j.get u
private theorem wordAt {n : ℕ} {f : Path (.word n) s} {v : Bits (s.size+1)} {u : Bits n} (h : At f v u) : evalWord (word f) v (value u).val := padded_spec _ _ _ fun i => h (.word i)
private theorem gateAt {v : Bits (s.size+1)} {f : Path (slot (width p) (GateSemantics.e p)) s} (r : CheckedRun (width p) p (GateSemantics.hd p)) (t : AuxBank (width p)) (h : At f v (rawRun r,t))
    {a x b : Word s} {A X B : ℕ} (ha : evalWord a v A) (hx : evalWord x v X) (hb : evalWord b v B) :
    (HashRows.block p (gw (GateSemantics.hd p) p a x b f)).OK v ↔ w3_slotHashBits (GateSemantics.hd p) A B X (R r).1.val (R r).2 (auxEquiv _ t) := by
  apply block_spec _ _ _ _ _ _ _ _ _ ha hx hb
  · change evalWord _ _ (Z r.1).val; rw [GateSemantics.resVal r.1.val r.1.property]; exact wordAt (fun j => h (.fst (.fst (.fst j))))
  · change evalWord _ _ ((finEquiv (fits p).le) r.2.1.1).val; rw [finEquiv_val]; exact wordAt (fun j => h (.fst (.snd (.fst (.fst (.fst j))))))
  all_goals first | exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.fst j)))))) | exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.snd (.fst (.fst j)))))))) | exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.snd (.snd (.fst j)))))))) | exact wordAt (fun j => h (.snd (.snd (.fst j)))) | skip
  · intro i; let j : Addr (slot (width p) (GateSemantics.e p)) := .fst (.snd (.snd .bit))
    change (p.testBit i && (Ref.reg (f j)).eval v) = (if r.2.2 then p else 0).testBit i
    rw [h j]; change (p.testBit i && r.2.2) = _; cases r.2.2 <;> simp
  all_goals funext i; first | simp only [gw,pad,dif_pos (show i.val < GateSemantics.e p from i.isLt)]; apply h | apply h
abbrev Slice (p : ℕ) := (Bool × Bounded (d:=width p) p × Bounded (d:=width p) p) × (Fin 4 → CheckedRun (width p) p (GateSemantics.hd p) × AuxBank (width p))
def sliceData (u : Slice p) : (mapShape (width p) (GateSemantics.e p)).Data := ((u.1.1,u.1.2.1.val,u.1.2.2.val),fun i => (rawRun (u.2 i).1,(u.2 i).2))
def output (u : Slice p) : Coords p := (u.1.1,Z u.1.2.1,Z u.1.2.2)
def cert (u : Slice p) : MapCert p := (R (u.2 0).1,R (u.2 1).1,R (u.2 2).1,R (u.2 3).1,())
private abbrev ga (u : Slice p) (i : Fin 4) : GateAux p := (auxEquiv _ (u.2 i).2,value (u.2 i).1.1.val.2.1,(u.2 i).1.1.val.2.2)
def auxBits (u : Slice p) := ((ga u 0,ga u 1,ga u 2,ga u 3,()),())
private theorem mask_spec {v : Bits (s.size+1)} {f : Ref s} {o z : Word s} {a b : ℕ} (O : evalWord o v a) (Z' : evalWord z v b) (n : ℕ) : (maskEq f o z n).OK v ↔
    ∀ i : Fin n, a.testBit i = (!f.eval v && b.testBit i) := by
  simp [maskEq,rows_iff]; apply forall_congr'; intro i; rw [O i,Z' i]
theorem mapBlock_iff (E : WeierstrassCurve (ZMod p)) (q : Coords p) (u : Slice p) (f : Path (mapShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
    (flag : Ref s) (x y : Word s) (H : At f v (sliceData u)) (F : flag.eval v = q.1) (X : evalWord x v q.2.1.val) (Y : evalWord y v q.2.2.val) :
    (mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val flag x y f).OK v ↔ (mapChecks E q (output u) (cert u)).bits (auxBits u) := by
  have bound {k : Path (triple (width p)) s} (w : Bounded (d:=width p) p) (h : At k v w.val) := (checker_iff p k v w.val h).2 w.property
  have ev {k : Path (triple (width p)) s} (w : Bounded (d:=width p) p) (h : At k v w.val) : evalWord (rwrd k) v (Z w).val := by
    rw [GateSemantics.resVal w.val w.property]; exact wordAt (fun j => h (.fst j))
  have O (i : Fin 4) : evalWord (rwrd (result (sp f i))) v (R (u.2 i).1).1.val := ev _ (fun j => H (.snd (.vec i (.fst (.fst j)))))
  have L (i : Fin 4) : w3_slotLt _ (R (u.2 i).1).1.val p (ga u i).2 := by
    change w3_slotLt _ (Z _).val _ _; rw [GateSemantics.resVal]; exact (below_iff _ _).1 (u.2 i).1.1.property
  have C : (ranges p f).OK v := by
    simp only [ranges,joinB_iff,many_iff]; exact ⟨⟨bound _ (fun j => H (.fst (.snd (.fst j)))),bound _ (fun j => H (.fst (.snd (.snd j))))⟩, fun i => ⟨bound _ (fun j => H (.snd (.vec i (.fst (.fst j))))),bound _ (fun j => H (.snd (.vec i (.fst (.snd (.fst (.fst j)))))))⟩⟩
  have G (i : Fin 4) := @gateAt _ _ _ v (sp f i) (u.2 i).1 (u.2 i).2 (fun j => H (.snd (.vec i j)))
  have P (n : ℕ) : evalWord (pub n) v n := fun _ => rfl; have M := @mask_spec _ v flag; have Mx := M (ev _ (fun j => H (.fst (.snd (.fst j))))) (O 0) (width p)
  have My := M (ev _ (fun j => H (.fst (.snd (.snd j))))) (O 3) (width p)
  have ff := H (.fst (.fst .bit)); change (Ref.reg _).eval v = u.1.1 at ff
  have b3 : (3*E.b₂).val = 3*E.b₂.val%p := by rw [ZMod.val_mul,ZMod.val_ofNat,Nat.mod_mul_mod]
  let ht (i : Fin 4) (a x b : ZMod p) := w3_slotHashBits (GateSemantics.hd p) a.val b.val x.val (R (u.2 i).1).1.val (R (u.2 i).1).2 (ga u i).1
  let lt (i : Fin 4) := w3_slotLt _ (R (u.2 i).1).1.val p (ga u i).2; let eqw (a b : ZMod p) := ∀ i : Fin (width p), a.val.testBit i = b.val.testBit i
  let dst : Coords p := if q.1 then (true,0,0) else (false,(R (u.2 0).1).1,(R (u.2 3).1).1)
  change _ ↔ (((ht 0 36 q.2.1 (3*E.b₂) ∧ lt 0) ∧ (ht 1 E.a₁ q.2.1 E.a₃ ∧ lt 1) ∧ (ht 2 2 q.2.2 (R (u.2 1).1).1 ∧ lt 2) ∧ (ht 3 108 (R (u.2 2).1).1 0 ∧ lt 3) ∧ True) ∧
    u.1.1 = dst.1 ∧ eqw (Z u.1.2.1) dst.2.1 ∧ eqw (Z u.1.2.2) dst.2.2)
  simp only [mapBlock,joinB_iff,C,true_and,many_iff,Fin.forall_fin_succ,Fin.forall_fin_zero, args4,Matrix.cons_val_zero,Matrix.cons_val_succ,eqs_iff,ff, and_true]
  rcases q with ⟨b,px,py⟩; cases b <;> simp [Mx,My,F,dst,ht,eqw,show ∀ i, lt i from L, ZMod.val_ofNat,b3,G 0 (P _) X (P _),G 1 (P _) X (P _),G 2 (P _) Y (O 1),G 3 (P _) (O 2) (P _)]
abbrev Witness (p : ℕ) := MapCert p × ((GateAux p × GateAux p × GateAux p × GateAux p × Unit) × Unit)
def pack (o : Coords p) (w : Witness p) : Slice p := ((o.1,Z.symm o.2.1,Z.symm o.2.2),fun i => (R.symm (![w.1.1,w.1.2.1,w.1.2.2.1,w.1.2.2.2.1] i),
    (auxEquiv _).symm (![w.2.1.1.1,w.2.1.2.1.1,w.2.1.2.2.1.1,w.2.1.2.2.2.1.1] i)))
theorem unpack (u : Slice p) : pack (output u) (cert u,auxBits u) = u := by
  exact Prod.ext (by simp [pack,output]) (by funext i; fin_cases i <;> simp [pack,cert,auxBits,ga])
theorem repack (E : WeierstrassCurve (ZMod p)) (q o : Coords p) (w : Witness p) (h : (mapChecks E q o w.1).bits w.2) : let u := pack o w
    output u = o ∧ (cert u,auxBits u) = w := by
  rcases w with ⟨⟨a,b,c,d,⟨⟩⟩,⟨A,B,C,D,⟨⟩⟩,⟨⟩⟩
  have eqGate (r : Run p) (t : GateAux p) (ht : w3_slotLt _ r.1.val p t.2) : let v := R.symm r; (auxEquiv _ ((auxEquiv _).symm t.1),value v.1.val.2.1,v.1.val.2.2) = t := by
    refine Prod.ext ((auxEquiv _).apply_symm_apply _) ?_
    let v := R.symm r; have hv : (Z v.1).val = r.1.val := congrArg (fun z : Run p => z.1.val) (R.apply_symm_apply r)
    rw [GateSemantics.resVal] at hv; obtain ⟨_,_,uniq⟩ := (w3_slotLt_spec (r.1.val_lt.trans (fits p)) (fits p).le).2 r.1.val_lt
    exact (uniq _ (hv ▸ (below_iff p v.1.val).1 v.1.property)).trans (uniq _ ht).symm
  have hA := eqGate a A h.1.1.2; have hB := eqGate b B h.1.2.1.2; have hC := eqGate c C h.1.2.2.1.2; have hD := eqGate d D h.1.2.2.2.1.2
  simp [pack,output,cert,auxBits,ga] at hA hB hC hD ⊢; simp only [hA,hB,hC,hD,and_self]
theorem mapBlock_unique (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p) (mul : w3_modMulInterface) (P : E.toAffine.Point) : ∃! u : Slice p, (mapChecks E (coords P) (output u) (cert u)).bits (auxBits u) := by
  let o := coords ((S8K.SWEquiv.equiv E (S8K.SWEquiv.six_ne_zero hp)) P)
  obtain ⟨w,hw,uw⟩ := ecToSW_unique_bits E hp mul P; obtain ⟨ho,he⟩ := repack E (coords P) o w hw
  refine ⟨pack o w,?_,?_⟩
  · change (mapChecks E (coords P) (output _) (cert _)).bits (auxBits _); rw [ho, (Prod.mk.inj he).1,(Prod.mk.inj he).2]; exact hw
  · intro v h; have hv : output v = o := ecToSW_sound E hp mul P _ _ ((ecToSW_lift E _ _ _).1 _ h)
    rw [hv] at h; rw [← unpack v,hv,uw (cert v,auxBits v) h]
/-- A slice is realizable independently of the enclosing register bank and its spare bit. -/
theorem acceptedSlice_unique (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (hp : 3 < p) (mul : w3_modMulInterface) (P : E.toAffine.Point) :
    ∃! w : (mapShape (width p) (GateSemantics.e p)).Data, ∃ (s : Shape) (f : Path _ s) (v : Bits (s.size+1)) (b : Ref s) (x y : Word s), At f v w ∧ b.eval v = (coords P).1 ∧ evalWord x v (coords P).2.1.val ∧
      evalWord y v (coords P).2.2.val ∧ (mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val b x y f).OK v := by
  obtain ⟨u,hu,unique⟩ := mapBlock_unique E hp mul P
  let S := mapShape (width p) (GateSemantics.e p); let v : Bits (S.size+1) := Fin.lastCases false (S.decode.symm (sliceData u))
  have h : At id v (sliceData u) := by intro j; change v j.index.castSucc = _; simp [v,← Addr.correct j (S.decode.symm (sliceData u))]
  refine ⟨sliceData u,⟨S,id,v,.pin (coords P).1,pub _,pub _,h,rfl,fun _ => rfl,fun _ => rfl, (mapBlock_iff E _ u id v _ _ _ h rfl (fun _ => rfl) (fun _ => rfl)).2 hu⟩,?_⟩
  rintro w ⟨s,f,z,b,x,y,H,F,X,Y,ok⟩; have hr := ((joinB_iff _ _ _).1 ok).1; change (ranges p f).OK z at hr
  simp only [ranges,joinB_iff,many_iff] at hr
  have bound {k : Path (triple (width p)) s} {a : Triple (width p)} (h : At k z a) := (checker_iff p k z a h).1
  let r (i : Fin 4) := (w.2 i).1
  let t : Slice p := ((w.1.1,⟨w.1.2.1,bound (fun j => H (.fst (.snd (.fst j)))) hr.1.1⟩,
    ⟨w.1.2.2,bound (fun j => H (.fst (.snd (.snd j)))) hr.1.2⟩),fun i => ((⟨(r i).1,bound (fun j => H (.snd (.vec i (.fst (.fst j))))) (hr.2 i).1⟩,
    (⟨(r i).2.1.1,bound (fun j => H (.snd (.vec i (.fst (.snd (.fst (.fst j))))))) (hr.2 i).2⟩,(r i).2.1.2),(r i).2.2),(w.2 i).2))
  exact congrArg sliceData (unique t ((mapBlock_iff E _ t f z b x y H F X Y).1 ok))
end
end DetDLP.S8M.ECMapRows


