-- Prove2me | Definitions.Def_DetDLP_S8H4_TracksPoly
-- name    : DetDLP_S8H4_TracksPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:02:06.87173+00:00
-- url     : https://prove2.me/theorems/4e0a6100-9e83-4762-92a1-b288bb729a98

import Definitions.Def_DetDLP_S8H0_OrderMake
import Definitions.Def_DetDLP_S8H4_BaseCode

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8H4.TracksPoly
open Groundwork S8H0 S8H.PointAddresses GateRoutes GateSemantics PointGraph RegisterMap NamedBlocks
open DetDLP.S8H4.Routes DetDLP.S8H4.Semantics

abbrev R := ℕ × (ℕ → ℕ)
def cat (a b : R) : R := (a.1+b.1, fun i => if i<a.1 then a.2 i else b.2 (i-a.1))
def manyR : (n : ℕ) → (Fin (n+1) → R) → R
  | 0,f => f 0
  | n+1,f => cat (f 0) (manyR n fun g => f g.succ)
def plusRows (n : ℕ) (a b z c : ℕ → ℕ) : R :=
  (n*5, fun i => let k := (S8H.PointAddresses.add n).bit i; let j := k/4
    if k%4=0 then a j else if k%4=1 then b j else if k%4=2 then z j else c j)
def pad (n t off i : ℕ) := if i<n then off+i else t
abbrev top (d e : ℕ) := (GateRoutes.S d e).size
abbrev newTop (d e : ℕ) := top d e + 4*d + 1
abbrev tri (d : ℕ) := (triple d).size
abbrev headN (d : ℕ) := 1+(tri d+tri d)
abbrev start (d e : ℕ) (g : Fin 7) := headN d + (run d e).size*g.val
def checkR (d e off : ℕ) : R :=
  plusRows (d+1) (pad d (top d e) off) (pad d (top d e) (off+d))
    (fun _ => top d e) (fun i => (off+d)+d+i)
def prodR (d e off : ℕ) (a b z : ℕ → ℕ) : R :=
  cat (e+e, fun i => off+(if i<e then i else i-e))
    ((4*d)*2, fun i => let j := i/2
      if i%2=0 then off+(if j<2*d then j else e-2*d+(j-2*d))
      else if j<d then a j else if j<2*d then b (j-d) else z (j-2*d))
def hashR' (d e t : ℕ) (g : Fin 7) (a x b : ℕ → ℕ) : R := Id.run do
  let o := start d e; let r := o g + tri d; let q := r+tri d; let m := q+d
  let m' := m+(2*d+e); let u := headN d+7*(run d e).size+(auxShape d).size*g.val
  let p1 := pad (2*d) t m; let p2 := pad (2*d) t m'
  let s := pad (d+1) t (u+2*d)
  return cat
    (cat (prodR d e (m+2*d) a x p1)
      (prodR d e (m'+2*d) (pad d t q) (fun _ => t) p2))
    (cat (plusRows (2*d) p2 (pad d t r) p1 (u+·))
      (cat (plusRows (d+1) (pad d t r) b s (u+2*d+(d+1)+·))
        (plusRows (d+1) (pad d t (o g)) (fun _ => m'+(2*d+e)) s
          (u+2*d+(d+1)+(d+1)+·))))
def hashR (d e : ℕ) (g : Fin 7) : R := Id.run do
  let t := top d e; let pub := fun _ : ℕ => t; let w := pad d t; let o := start d e
  let (a,x,b) := ![(pub,w 1,w (1+tri d)),(pub,w (o 0),pub),(w (o 1),w (1+tri d),pub),
    (pub,w 1,pub),(w (o 3),w 1,pub),(w (o 4),w 1,pub),(pub,w 1,pub)] g
  return hashR' d e t g a x b
def rangesR (d e : ℕ) : R :=
  let f := checkR d e; let o := start d e
  cat (cat (f 1) (f (1+tri d))) (manyR 6 fun g => cat (f (o g)) (f (o g+tri d)))
def curveR (d e : ℕ) : R :=
  (d*5, fun i => let j := i/5; if i%5=0 then 0 else if i%5=1 then 1+j
    else if i%5=2 then 1+tri d+j else if i%5=3 then start d e 2+j else start d e 5+j)
def baseR (d e : ℕ) : R :=
  cat (rangesR d e) (cat (manyR 5 fun g => hashR d e g.castSucc) (curveR d e))
def remap (a : R) (old new : ℕ) : R := (a.1,fun i => if a.2 i=old then new else a.2 i)
def hash6R (d e : ℕ) : R :=
  hashR' d e (newTop d e) ⟨6,by decide⟩
    (pad d (newTop d e) (top d e)) (pad d (newTop d e) 1)
    (pad d (newTop d e) (top d e+d))
def muxR (d e : ℕ) : R := (d*3,fun i => let j := i/3
  if i%3=0 then 1+tri d else if i%3=1 then top d e+j else top d e+d+j)
def flagR (_d _e : ℕ) : R := (1,fun _ => 0)
def ltR (d e : ℕ) : R := plusRows (d+1)
  (pad d (newTop d e) (start d e 6))
  (pad d (newTop d e) (top d e+2*d))
  (fun _ => newTop d e) (fun i => top d e+3*d+i)
def preR (d e b l : ℕ) : R := (l,fun i =>
  if i=0 then 0 else if i-1<b then 1+(b-1-(i-1))
  else if i-1-b<b then 1+tri d+(b-1-(i-1-b)) else newTop d e)
def route (d e b l : ℕ) : R :=
  cat (newTop d e+1,id)
    (cat (1,fun _ => newTop d e)
      (cat (remap (baseR d e) (top d e) (newTop d e))
        (cat (hash6R d e) (cat (muxR d e)
          (cat (flagR d e) (cat (ltR d e) (preR d e b l)))))))
def sigNat (d e b l i : ℕ) : ℕ := (route d e b l).2 i

set_option maxHeartbeats 900000
attribute [local fun_prop] PolyT.mul PolyT.div PolyT.mod PolyT.sub PolyT.ite' PolyT.decide_lt PolyT.decide_eq PolyT.const PolyT.comp PolyT.id' PolyT.fst PolyT.snd w4_M5Evaluator.clog2_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
def Good {α} [Enc α] (f : α → R) := PolyT (fun x => (f x).1) ∧ ∀ i : α → ℕ, PolyT i → PolyT fun x => (f x).2 (i x)
private theorem catP {α} [Enc α] {a b : α → R} (h : Good a) (j : Good b) : Good fun x => cat (a x) (b x) :=
  ⟨PolyT.add h.1 j.1, fun i hi => PolyT.ite' (PolyT.decide_lt hi h.1) (h.2 _ hi) (j.2 _ (PolyT.sub hi h.1))⟩
private theorem manyP {α} [Enc α] (n) (f : α → Fin (n+1) → R) (h : ∀ g, Good fun x => f x g) : Good fun x => manyR n (f x) := by
  induction n with | zero => exact h 0 | succ n ih => exact catP (h 0) (ih _ fun g => h g.succ)
private theorem remapP {α} [Enc α] {a : α → R} {o n : α → ℕ} (ha : Good a) (ho : PolyT o) (hn : PolyT n) : Good fun x => remap (a x) (o x) (n x) :=
  ⟨ha.1, fun i hi => PolyT.ite' (PolyT.decide_eq (ha.2 i hi) ho) hn (ha.2 i hi)⟩
private abbrev PW {α} [Enc α] (f : α → ℕ → ℕ) := ∀ {i : α → ℕ}, PolyT i → PolyT fun x => f x (i x)
private theorem plusP {α} [Enc α] {n : α → ℕ} {a b z c : α → ℕ → ℕ} (hn : PolyT n) (ha : PW a) (hb : PW b) (hz : PW z) (hc : PW c) : Good fun x => plusRows (n x) (a x) (b x) (z x) (c x) := by
  refine ⟨PolyT.mul hn (PolyT.const 5),?_⟩; intro i hi; let k x := (S8H.PointAddresses.add (n x)).bit (i x); have hk := add_poly id (by intros; assumption) |>.bit hn hi; have h : PolyT k := hk; have j := PolyT.div h (PolyT.const 4); have m := PolyT.mod h (PolyT.const 4)
  exact PolyT.ite' (PolyT.decide_eq m (PolyT.const 0)) (ha j) (PolyT.ite' (PolyT.decide_eq m (PolyT.const 1)) (hb j) (PolyT.ite' (PolyT.decide_eq m (PolyT.const 2)) (hz j) (hc j)))
private theorem prodP {α} [Enc α] {d e o : α → ℕ} {a b z : α → ℕ → ℕ} (hd : PolyT d) (he : PolyT e) (ho : PolyT o) (ha : PW a) (hb : PW b) (hz : PW z) : Good fun x => prodR (d x) (e x) (o x) (a x) (b x) (z x) := by
  apply catP
  · exact ⟨PolyT.add he he,fun i hi => PolyT.add ho (PolyT.ite' (PolyT.decide_lt hi he) hi (PolyT.sub hi he))⟩
  · refine ⟨by dsimp; fun_prop,fun i hi => ?_⟩; have j := PolyT.div hi (PolyT.const 2); have t := PolyT.mul (PolyT.const 2) hd
    exact PolyT.ite' (PolyT.decide_eq (PolyT.mod hi (PolyT.const 2)) (PolyT.const 0)) (PolyT.add ho (PolyT.ite' (PolyT.decide_lt j t) j (PolyT.add (PolyT.sub he t) (PolyT.sub j t)))) (PolyT.ite' (PolyT.decide_lt j hd) (ha j) (PolyT.ite' (PolyT.decide_lt j t) (hb (PolyT.sub j hd)) (hz (PolyT.sub j t))))
private theorem tri_eq (d : ℕ) : tri d = 3*d+1 := by simp only [tri,triple,Shape.size]; omega
private theorem run_eq (d e : ℕ) : (run d e).size = 11*d+2*e+3 := by simp only [run,triple,RegisterMap.mul,Shape.size]; omega
private theorem aux_eq (d : ℕ) : (auxShape d).size = 5*d+3 := by simp only [auxShape,Shape.size]; omega
private theorem top_eq (d e : ℕ) : top d e = 118*d+14*e+45 := by simp only [top,GateRoutes.S,RegisterMap.bank,run_eq,aux_eq,triple,Shape.size]; omega

private theorem hashR'_poly {α} [Enc α] {D E T : α → ℕ} (hD : PolyT D) (hE : PolyT E) (hT : PolyT T) (g : Fin 7) {a x b : α → ℕ → ℕ} (ha : PW a) (hx : PW x) (hb : PW b) : Good fun z => hashR' (D z) (E z) (T z) g (a z) (x z) (b z) := by
  unfold hashR'
  refine catP (catP (prodP hD hE ?_ ha hx ?_) (prodP hD hE ?_ ?_ ?_ ?_)) (catP (plusP ?_ ?_ ?_ ?_ ?_) (catP (plusP ?_ ?_ hb ?_ ?_) (plusP ?_ ?_ ?_ ?_ ?_))) <;>
    ((try (unfold PW; intros)); (try simp only [pad,start,headN,Id.run,tri_eq,run_eq,aux_eq,top_eq]); first | assumption | fun_prop (disch := assumption))

theorem sigNat_poly {α : Type} [Enc α] {D E B L I : α → ℕ} (hD : PolyT D) (hE : PolyT E) (hB : PolyT B) (hL : PolyT L) (hI : PolyT I) :
    PolyT fun x => sigNat (D x) (E x) (B x) (L x) (I x) := by
  have hc (off : α → ℕ) (h : PolyT off) : Good fun x => checkR (D x) (E x) (off x) := by
    apply plusP (PolyT.add hD (PolyT.const 1)) <;> ((try (unfold PW; intros)); (try simp only [pad,start,headN,Id.run,tri_eq,run_eq,aux_eq,top_eq]); first | assumption | fun_prop (disch := assumption))
  have hTop : PolyT fun x => top (D x) (E x) := by simp only [top_eq]; fun_prop (disch := assumption)
  have hNew : PolyT fun x => newTop (D x) (E x) := by simp only [newTop,top_eq]; fun_prop (disch := assumption)
  have hh (g : Fin 6) : Good fun x => hashR (D x) (E x) g.castSucc := by
    fin_cases g <;> exact hashR'_poly hD hE hTop _
      (by unfold PW; intros; (try simp only [pad,start,headN,Id.run,tri_eq,run_eq,aux_eq,top_eq]); fun_prop (disch := assumption))
      (by unfold PW; intros; (try simp only [pad,start,headN,Id.run,tri_eq,run_eq,aux_eq,top_eq]); fun_prop (disch := assumption))
      (by unfold PW; intros; (try simp only [pad,start,headN,Id.run,tri_eq,run_eq,aux_eq,top_eq]); fun_prop (disch := assumption))
  have hh6 : Good fun x => hash6R (D x) (E x) :=
    hashR'_poly hD hE hNew ⟨6, by decide⟩
      (by unfold PW; intros; (try simp only [pad,newTop,top_eq]); fun_prop (disch := assumption))
      (by unfold PW; intros; (try simp only [pad,newTop,top_eq]); fun_prop (disch := assumption))
      (by unfold PW; intros; (try simp only [pad,newTop,top_eq]); fun_prop (disch := assumption))
  have hlt : Good fun x => ltR (D x) (E x) := by
    unfold ltR
    apply plusP (PolyT.add hD (PolyT.const 1)) <;> ((try (unfold PW; intros)); (try simp only [pad,start,headN,newTop,tri_eq,run_eq,aux_eq,top_eq]); first | assumption | fun_prop (disch := assumption))
  have hbase : Good fun x => baseR (D x) (E x) := by
    refine catP (catP (catP (hc _ ?_) (hc _ ?_)) (manyP _ _ fun g => catP (hc _ ?_) (hc _ ?_))) (catP (manyP _ _ hh) ?_)
    all_goals first
      | constructor <;> (intros; (try simp only [curveR,pad,start,headN,tri_eq,run_eq,aux_eq,top_eq]); fun_prop (disch := assumption))
      | ((try simp only [start,headN,tri_eq,run_eq,aux_eq,top_eq]); fun_prop (disch := assumption))
  have hpre : Good fun x => preR (D x) (E x) (B x) (L x) := by
    refine ⟨hL, fun i hi => ?_⟩; dsimp only [preR]
    exact PolyT.ite' (PolyT.decide_eq hi (PolyT.const 0)) (PolyT.const 0)
      (PolyT.ite' (PolyT.decide_lt (PolyT.sub hi (PolyT.const 1)) hB)
        (PolyT.add (PolyT.const 1) (PolyT.sub (PolyT.sub hB (PolyT.const 1)) (PolyT.sub hi (PolyT.const 1))))
        (PolyT.ite' (PolyT.decide_lt (PolyT.sub (PolyT.sub hi (PolyT.const 1)) hB) hB)
          (PolyT.add (PolyT.add (PolyT.const 1) (by simp only [tri_eq]; fun_prop (disch := assumption)))
            (PolyT.sub (PolyT.sub hB (PolyT.const 1)) (PolyT.sub (PolyT.sub hi (PolyT.const 1)) hB)))
          hNew))
  have hr : Good fun x => route (D x) (E x) (B x) (L x) := by
    refine catP ?_ (catP ?_ (catP (remapP hbase hTop hNew) (catP hh6 (catP ?_ (catP ?_ (catP hlt hpre))))))
    all_goals constructor <;> (intros; (try simp only [muxR,flagR,id,newTop,tri_eq,run_eq,aux_eq,top_eq]); fun_prop (disch := assumption))
  exact hr.2 I hI

end DetDLP.S8H4.TracksPoly


