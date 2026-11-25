-- Prove2me | Definitions.Def_DetDLP_M3B_ECMapRows
-- name    : DetDLP_M3B_ECMapRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T12:59:38.92831+00:00
-- url     : https://prove2.me/theorems/81699939-c73d-40bb-9ab1-b449c26cfa44
-- title:
--   EC unpinned map rows
-- statement:
--   Unpinned S8H0 register block for ecToSW coordinate conversion
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8O_ECAddLayout
import Definitions.Def_DetDLP_S8H0_GateSemantics

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.M3B.ECMapRows
open S8H0 RegisterMap NamedBlocks ResidueWires SignalBank HashRows RangeRows GateRoutes
open S8H.ECPointArithmetic S8K.ECAddArithmetic S8O.ECAddLayout
variable {d e : ℕ} {s : Shape}
variable {p : ℕ} [Fact p.Prime]

structure Clause (W : Type) where
  residue : Prop
  bits : W → Prop
  lift : w3_slotLift residue bits

def both {A B : Type} (a : Clause A) (b : Clause B) : Clause (A × B) :=
  ⟨a.residue ∧ b.residue, fun w => a.bits w.1 ∧ b.bits w.2, w3_slotLiftProd a.lift b.lift⟩
def plain (P Q : Prop) (h : P ↔ Q) : Clause Unit :=
  ⟨P, fun _ => Q, fun _ => h.mpr, fun hp => ⟨(),h.mp hp,fun _ _ => rfl⟩⟩
def wordEq (x y : ZMod p) := ∀ i : Fin (width p), x.val.testBit i = y.val.testBit i
 theorem eq_bits (x y : ZMod p) : x = y ↔ wordEq x y := by
  refine ⟨fun e _ => e ▸ rfl, fun h => ZMod.val_injective p (Nat.eq_of_testBit_eq fun i => ?_)⟩
  by_cases hi : i < width p
  · exact h ⟨i,hi⟩
  · have H := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_eq_false_of_lt (x.val_lt.trans_le ((fits p).le.trans H)),
        Nat.testBit_eq_false_of_lt (y.val_lt.trans_le ((fits p).le.trans H))]
def finalCoords (out expected : Coords p) := plain (out = expected)
  (out.1 = expected.1 ∧ wordEq out.2.1 expected.2.1 ∧ wordEq out.2.2 expected.2.2)
  (by simp only [← eq_bits, Prod.ext_iff])
abbrev GateAux (p : ℕ) := w3_slotHashAux (width p) × w3_slotDiff (width p)
def hash (a x b : ZMod p) (r : Run p) : Clause (GateAux p) where
  residue := gate a x b r.1 r.2
  bits w := w3_slotHashBits (Nat.succ_pos _) a.val b.val x.val r.1.val r.2 w.1 ∧
    w3_slotLt (width p) r.1.val p w.2
  lift := by
    have H := w3_slotHash_spec (a := a.val) (x := x.val) (Nat.succ_pos _) (fits p) b.val_lt r.1.val_lt r.2
    have L := w3_slotLt_spec (r.1.val_lt.trans (fits p)) (fits p).le
    exact ⟨fun w h => H.1 w.1 h.1, fun hr => (w3_slotLiftProd H L).2 ⟨hr,r.1.val_lt⟩⟩
def mapChecks' (E : WeierstrassCurve (ZMod p)) (P out : Coords p) (c : MapCert p) :=
  let (i,x,y) := P; let (X,t,u,Y,_) := c
  both (both (hash 36 x (3*E.b₂) X) (both (hash E.a₁ x E.a₃ t)
    (both (hash 2 y t.1 u) (both (hash 108 u.1 0 Y) (plain True True Iff.rfl)))))
    (finalCoords out (if i then (true,0,0) else (false,X.1,Y.1)))
abbrev slot (d e : ℕ) := Shape.pair (run d e) (auxShape d)
def mapShape (d e : ℕ) := Shape.pair (.pair .bit (.pair (triple d) (triple d))) (.vec 4 (slot d e))
abbrev fstP {a b : Shape} (f : Path (.pair a b) s) : Path a s := fun j => f (.fst j)
abbrev sndP {a b : Shape} (f : Path (.pair a b) s) : Path b s := fun j => f (.snd j)
abbrev rwrd (f : Path (triple d) s) := word (fstP f)
abbrev refw {n : ℕ} (f : Path (.word n) s) (i : Fin n) : Ref s := .reg (f (.word i))
def gw (hd : 1 ≤ d) (p : ℕ) (a x b : Word s) (f : Path (slot d e) s) : Wires d hd s :=
  let r := fstP f; let k := fstP (sndP r); let l := sndP k; let m := sndP l; let t := sndP f
  ⟨a,x,b,rwrd (fstP r),rwrd (fstP k),word (fstP l),word (fstP (fstP m)),word (fstP (sndP m)),
   word (fstP (sndP t)),fun i => .masked (p.testBit i) (sndP (sndP r) .bit),
   pad (refw (sndP (fstP m))),pad (refw (sndP (sndP m))),refw (fstP t),
   refw (fstP (sndP (sndP t))),refw (sndP (sndP (sndP t)))⟩
/-- A slot with too few multiplier incidences cannot encode an accepting gate. -/
def slotBlock (hd : 1 ≤ d) (p : ℕ) (a x b : Word s) (f : Path (slot d e) s) : B (s.size+1) :=
  if (w4_M5GraphBounds.graph d hd).nE ≤ e then HashRows.block p (gw hd p a x b f)
  else rows 1 1 (fun _ _ => .pin false) (fun _ _ => false)
private abbrev sp (f : Path (mapShape d e) s) (g : Fin 4) : Path (slot d e) s := fun j => f (.snd (.vec g j))
abbrev result (f : Path (slot d e) s) := fstP (fstP f)
abbrev remain (f : Path (slot d e) s) := fstP (fstP (sndP (fstP f)))
private def maskEq (f : Ref s) (o z : Word s) (d : ℕ) := rows d 3
  (fun i => ![f,o i,z i]) (fun _ v => v 1 == (!v 0 && v 2))
private abbrev args4 (p b2 a1 a3 : ℕ) (x y : Word s) (f : Path (mapShape d e) s) : Fin 4 → Word s × Word s × Word s :=
  let z := fun i => rwrd (result (sp f i))
  ![(pub (36%p),x,pub (3*b2%p)),(pub a1,x,pub a3),(pub (2%p),y,z 1),(pub (108%p),z 2,pub 0)]
private def ranges (p : ℕ) (f : Path (mapShape d e) s) :=
  let o := sndP (fstP f)
  joinB (joinB (checker p (fstP o)) (checker p (sndP o)))
    (many 3 fun i => joinB (checker p (result (sp f i))) (checker p (remain (sp f i))))
def mapBlock (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (inFlag : Ref s) (inX inY : Word s)
    (path : Path (mapShape d e) s) : B (s.size+1) :=
  let o := sndP (fstP path); let z := fun i => rwrd (result (sp path i))
  joinB (ranges p path) (joinB (many 3 fun i => let a := args4 p b2 a1 a3 inX inY path i
    slotBlock hd p a.1 a.2.1 a.2.2 (sp path i)) (joinB
    (eqs 1 (fun _ => .reg (fstP (fstP path) .bit)) (fun _ => inFlag))
    (joinB (maskEq inFlag (rwrd (fstP o)) (z 0) d) (maskEq inFlag (rwrd (sndP o)) (z 3) d))))

noncomputable section
abbrev R := runEquiv (GateSemantics.hd p) (fits p).le
abbrev Z := zmodEquiv (fits p).le
abbrev rawRun (r : CheckedRun (width p) p (GateSemantics.hd p)) : (run (width p) (GateSemantics.e p)).Data :=
  (r.1.val, (r.2.1.1.val,r.2.1.2),r.2.2)
def At {q : Shape} (f : Path q s) (v : Bits (s.size+1)) (u : q.Data) := ∀ j, (Ref.reg (f j)).eval v = j.get u
theorem wordAt {n : ℕ} {f : Path (.word n) s} {v : Bits (s.size+1)} {u : Bits n} (h : At f v u) :
    evalWord (word f) v (value u).val := padded_spec _ _ _ fun i => h (.word i)
theorem gateAt {v : Bits (s.size+1)} {f : Path (slot (width p) (GateSemantics.e p)) s}
    (r : CheckedRun (width p) p (GateSemantics.hd p)) (t : AuxBank (width p)) (h : At f v (rawRun r,t))
    {a x b : Word s} {A X B : ℕ} (ha : evalWord a v A) (hx : evalWord x v X) (hb : evalWord b v B) :
    (HashRows.block p (gw (GateSemantics.hd p) p a x b f)).OK v ↔
    w3_slotHashBits (GateSemantics.hd p) A B X (R r).1.val (R r).2 (auxEquiv _ t) := by
  apply block_spec _ _ _ _ _ _ _ _ _ ha hx hb
  · change evalWord _ _ (Z r.1).val; rw [GateSemantics.resVal r.1.val r.1.property]; exact wordAt (fun j => h (.fst (.fst (.fst j))))
  · change evalWord _ _ ((finEquiv (fits p).le) r.2.1.1).val; rw [finEquiv_val]; exact wordAt (fun j => h (.fst (.snd (.fst (.fst (.fst j))))))
  · exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.fst j))))))
  · exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.snd (.fst (.fst j))))))))
  · exact wordAt (fun j => h (.fst (.snd (.fst (.snd (.snd (.snd (.fst j))))))))
  · exact wordAt (fun j => h (.snd (.snd (.fst j))))
  · intro i; let j : Addr (slot (width p) (GateSemantics.e p)) := .fst (.snd (.snd .bit))
    change (p.testBit i && (Ref.reg (f j)).eval v) = (if r.2.2 then p else 0).testBit i
    rw [h j]; change (p.testBit i && r.2.2) = _; cases r.2.2 <;> simp
  · funext i; simp only [gw,pad,dif_pos (show i.val < GateSemantics.e p from i.isLt)]; apply h
  · funext i; simp only [gw,pad,dif_pos (show i.val < GateSemantics.e p from i.isLt)]; apply h
  · funext i; exact h (.snd (.fst (.word i)))
  · funext i; exact h (.snd (.snd (.snd (.fst (.word i)))))
  · funext i; exact h (.snd (.snd (.snd (.snd (.word i)))))
abbrev Slice (p : ℕ) := (Bool × Bounded (d:=width p) p × Bounded (d:=width p) p) ×
  (Fin 4 → CheckedRun (width p) p (GateSemantics.hd p) × AuxBank (width p))
def sliceData (u : Slice p) : (mapShape (width p) (GateSemantics.e p)).Data :=
  ((u.1.1,u.1.2.1.val,u.1.2.2.val),fun i => (rawRun (u.2 i).1,(u.2 i).2))
def output (u : Slice p) : Coords p := (u.1.1,Z u.1.2.1,Z u.1.2.2)
def cert (u : Slice p) : MapCert p := (R (u.2 0).1,R (u.2 1).1,R (u.2 2).1,R (u.2 3).1,())
private abbrev ga (u : Slice p) (i : Fin 4) : GateAux p :=
  (auxEquiv _ (u.2 i).2,value (u.2 i).1.1.val.2.1,(u.2 i).1.1.val.2.2)
def auxBits (u : Slice p) := ((ga u 0,ga u 1,ga u 2,ga u 3,()),())
private theorem mask_spec {v : Bits (s.size+1)} {f : Ref s} {o z : Word s} {a b : ℕ}
    (O : evalWord o v a) (Z' : evalWord z v b) (n : ℕ) : (maskEq f o z n).OK v ↔
    ∀ i : Fin n, a.testBit i = (!f.eval v && b.testBit i) := by
  rw [maskEq, rows_iff]
  constructor
  · intro h i; simpa [O i, Z' i] using h i
  · intro h i; simpa [O i, Z' i] using h i
theorem mapBlock_iff (E : WeierstrassCurve (ZMod p)) (q : Coords p) (u : Slice p)
    (f : Path (mapShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
    (flag : Ref s) (x y : Word s) (H : At f v (sliceData u)) (F : flag.eval v = q.1)
    (X : evalWord x v q.2.1.val) (Y : evalWord y v q.2.2.val) :
    (mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val flag x y f).OK v ↔
    (mapChecks' E q (output u) (cert u)).bits (auxBits u) := by
  have bound {k : Path (triple (width p)) s} (w : Bounded (d:=width p) p) (h : At k v w.val) := (checker_iff p k v w.val h).2 w.property
  have ev {k : Path (triple (width p)) s} (w : Bounded (d:=width p) p) (h : At k v w.val) : evalWord (rwrd k) v (Z w).val := by
    rw [GateSemantics.resVal w.val w.property]; exact wordAt (fun j => h (.fst j))
  have O (i : Fin 4) : evalWord (rwrd (result (sp f i))) v (R (u.2 i).1).1.val := ev _ (fun j => H (.snd (.vec i (.fst (.fst j)))))
  have L (i : Fin 4) : w3_slotLt _ (R (u.2 i).1).1.val p (ga u i).2 := by
    change w3_slotLt _ (Z _).val _ _; rw [GateSemantics.resVal]; exact (below_iff _ _).1 (u.2 i).1.1.property
  have C : (ranges p f).OK v := by
    simp only [ranges,joinB_iff,many_iff]; exact ⟨⟨bound _ (fun j => H (.fst (.snd (.fst j)))),bound _ (fun j => H (.fst (.snd (.snd j))))⟩,
      fun i => ⟨bound _ (fun j => H (.snd (.vec i (.fst (.fst j))))),bound _ (fun j => H (.snd (.vec i (.fst (.snd (.fst (.fst j)))))))⟩⟩
  have G (i : Fin 4) := @gateAt _ _ _ v (sp f i) (u.2 i).1 (u.2 i).2 (fun j => H (.snd (.vec i j)))
  have P (n : ℕ) : evalWord (pub n) v n := fun _ => rfl
  have M := @mask_spec _ v flag; have Mx := M (ev _ (fun j => H (.fst (.snd (.fst j))))) (O 0) (width p)
  have My := M (ev _ (fun j => H (.fst (.snd (.snd j))))) (O 3) (width p)
  have ff := H (.fst (.fst .bit)); change (Ref.reg _).eval v = u.1.1 at ff
  have b3 : (3*E.b₂).val = 3*E.b₂.val%p := by rw [ZMod.val_mul,ZMod.val_ofNat,Nat.mod_mul_mod]
  rcases q with ⟨b,px,py⟩; cases b <;>
    simp only [mapBlock,joinB_iff,C,true_and,many_iff,Fin.forall_fin_succ,Fin.forall_fin_zero,slotBlock,GateSemantics.e,le_refl,if_true,
      args4,Matrix.cons_val_zero,Matrix.cons_val_succ,eqs_iff,ff,F] <;>
    simp [mapChecks', output, cert, auxBits, both, hash, finalCoords, plain, wordEq, ZMod.val_ofNat,
      Mx, My, b3, L, G 0 (P _) X (P _), G 1 (P _) X (P _), G 2 (P _) Y (O 1),
      G 3 (P _) (O 2) (P _), F, ff, ga] <;> aesop
theorem mapChecks_lift (E : WeierstrassCurve (ZMod p)) (q out : Coords p) (c : MapCert p) :
    w3_slotLift (ecToSWOK E q out c) (mapChecks' E q out c).bits := (mapChecks' E q out c).lift

theorem mapBlock_sound (E : WeierstrassCurve (ZMod p)) (q : Coords p) (u : Slice p)
    (f : Path (mapShape (width p) (GateSemantics.e p)) s) (v : Bits (s.size+1))
    (flag : Ref s) (x y : Word s) (H : At f v (sliceData u)) (F : flag.eval v = q.1)
    (X : evalWord x v q.2.1.val) (Y : evalWord y v q.2.2.val)
    (h : (mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val flag x y f).OK v) :
    ecToSWOK E q (output u) (cert u) :=
  (mapChecks_lift E q _ _).1 _ ((mapBlock_iff E q u f v flag x y H F X Y).mp h)

theorem mapBlock_edges (hd : 1 ≤ d) (p b2 a1 a3 : ℕ) (inFlag : Ref s) (inX inY : Word s)
    (path : Path (mapShape d e) s) :
    (mapBlock hd p b2 a1 a3 inFlag inX inY path).core.A.ne ≤ 16*e + 400*(d+2) := by
  by_cases h : (w4_M5GraphBounds.graph d hd).nE ≤ e <;>
    simp only [slotBlock,h,if_true,if_false,mapBlock, ranges, maskEq, HashRows.block, many, joinB, HashRows.product, eqs,
    HashRows.sumRows, checker, NamedBlocks.add, rows, mapped, S8J.join, S8C.AddLayout.layout,
    AnchoredLayout.anchors,w3_fpMulLayout,w3_m5Layout,w3_forgetSides] <;> omega
end
end DetDLP.M3B.ECMapRows


