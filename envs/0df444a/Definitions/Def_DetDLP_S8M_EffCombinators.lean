-- Prove2me | Definitions.Def_DetDLP_S8M_EffCombinators
-- name    : DetDLP_S8M_EffCombinators
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:03:23.374806+00:00
-- url     : https://prove2.me/theorems/6ebf5319-604c-437b-b7f6-0ab37db848a6

import Definitions.Def_DetDLP_S8H_MakeCombinators
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.EffCombinators
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1 S8H.MakeCombinators
def wd (o n pin j : ℕ) := if j < n then o + j else pin
def rangeN (d pin o : ℕ) := colN (d+1) (wd o d pin) (wd (o+d) d pin) (fun _ => pin) (o+2*d+·)
def repCode (n : ℕ) (c : Code) (f : ℕ → ℕ → ℕ) : NC :=
  (⟨n*c.ng, n*c.nb, n*c.ne, fun i => i/c.ne*c.ng + c.gate (i%c.ne), fun i => i/c.ne*c.nb + c.bit (i%c.ne)⟩, fun i => f (i/c.ne) (i%c.ne))
def repeated (n : ℕ) (f : ℕ → NC) : NC := repCode n (f 0).1 (fun j => (f j).2)
theorem wiresP {α : Type} [Enc α] {D : α → ℕ} (h : PolyT D) : PolyT fun x => wires (D x) := mul_poly.nb h
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.div PolyT.mod PolyT.length w4_M5Evaluator.clog2_poly w4_M5Evaluator.vertexCount_poly w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly
attribute [local fun_prop] wiresP P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 PolyT.decide_lt PolyT.decide_eq
theorem repP {α : Type} [Enc α] {K : α → ℕ} {F : α → ℕ → NC} (hk : PolyT K) (hf : ∀ {J : α → ℕ}, PolyT J → Eff (fun x => F x (J x))) : Eff (fun x => repeated (K x) (F x)) := by
  have z := hf (PolyT.const (0:ℕ)); refine ⟨PolyT.mul hk z.1,PolyT.mul hk z.2.1,fun hi => ?_⟩
  have q := PolyT.div hi z.2.1; have r := PolyT.mod hi z.2.1
  exact ⟨PolyT.add (PolyT.mul q z.1) ((z.2.2 r).1),((hf q).2.2 r).2⟩
abbrev FP {α : Type} [Enc α] (F : α → ℕ → ℕ) := ∀ {J : α → ℕ}, PolyT J → PolyT fun x => F x (J x)
theorem rowP {α : Type} [Enc α] {N M : α → ℕ} {F : α → ℕ → ℕ → ℕ} (hn : PolyT N) (hm : PolyT M) (hf : ∀ {J K : α → ℕ}, PolyT J → PolyT K → PolyT fun x => F x (J x) (K x)) : Eff (fun x => rowN (N x) (M x) (F x)) := ⟨hn,PolyT.mul hn hm,fun hi => ⟨PolyT.div hi hm,hf (PolyT.div hi hm) (PolyT.mod hi hm)⟩⟩
theorem colP {α : Type} [Enc α] {N : α → ℕ} {A B Z C : α → ℕ → ℕ} (hn : PolyT N) (ha : FP A) (hb : FP B) (hz : FP Z) (hc : FP C) : Eff (fun x => colN (N x) (A x) (B x) (Z x) (C x)) := by
  have U := add_poly id (by intros; assumption)
  refine ⟨hn,PolyT.mul hn (PolyT.const 5),fun {I} hi => ⟨PolyT.div hi (PolyT.const 5),?_⟩⟩
  have hk : PolyT fun x => (S8H.PointAddresses.add (N x)).bit (I x) := U.bit hn hi
  have hj := PolyT.div hk (PolyT.const 4); have hr := PolyT.mod hk (PolyT.const 4)
  exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hr (PolyT.const 0)) (ha hj) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hr (PolyT.const 1)) (hb hj) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hr (PolyT.const 2)) (hz hj) (hc hj)))
theorem prodP {α : Type} [Enc α] {D E O : α → ℕ} {A B Z : α → ℕ → ℕ} (hd : PolyT D) (he : PolyT E) (ho : PolyT O) (ha : FP A) (hb : FP B) (hz : FP Z) : Eff (fun x => prodN (D x) (E x) (O x) (A x) (B x) (Z x)) := by
  unfold prodN; refine catP ⟨mul_poly.ng hd,mul_poly.ne hd,fun hi => ⟨mul_poly.gate hd hi,?_⟩⟩ (rowP (PolyT.mul (PolyT.const 4) hd) (PolyT.const 2) ?_)
  · exact PolyT.add ho (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hi he) hi (PolyT.sub hi he))
  · intro J K hj hk
    have hh := PolyT.mul (PolyT.const 2) hd
    exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hk (PolyT.const 0)) (PolyT.add ho (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hh) hj (PolyT.add (PolyT.sub he hh) (PolyT.sub hj hh)))) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hd) (ha hj) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hh) (hb (PolyT.sub hj hd)) (hz (PolyT.sub hj hh))))
theorem wdP {α : Type} [Enc α] {O N P J : α → ℕ} (ho : PolyT O) (hn : PolyT N) (hp : PolyT P) (hj : PolyT J) : PolyT fun x => wd (O x) (N x) (P x) (J x) := P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hn) (PolyT.add ho hj) hp
theorem rangeP {α : Type} [Enc α] {D P O : α → ℕ} (hd : PolyT D) (hp : PolyT P) (ho : PolyT O) : Eff (fun x => rangeN (D x) (P x) (O x)) := colP (PolyT.add hd (PolyT.const 1)) (fun h => wdP ho hd hp h) (fun h => wdP (PolyT.add ho hd) hd hp h) (fun _ => hp) (fun h => PolyT.add (PolyT.add ho (PolyT.mul (PolyT.const 2) hd)) h)
theorem genHashP {α : Type} [Enc α] {D E O1 O2 P : α → ℕ} {A X B Z R Q P1 P2 S CP C1 C2 C3 : α → ℕ → ℕ}
    (hd : PolyT D) (he : PolyT E) (ho1 : PolyT O1) (ho2 : PolyT O2) (hp : PolyT P)
    (ha : FP A) (hx : FP X) (hb : FP B) (hz : FP Z) (hr : FP R) (hq : FP Q)
    (hp1 : FP P1) (hp2 : FP P2) (hs : FP S) (hcp : FP CP) (hc1 : FP C1) (hc2 : FP C2) (hc3 : FP C3) :
    Eff (fun x => genHashN (D x) (E x) (O1 x) (O2 x) (P x) (A x) (X x) (B x) (Z x) (R x) (Q x) (P1 x) (P2 x) (S x) (CP x) (C1 x) (C2 x) (C3 x)) :=
  catP (catP (prodP hd he ho1 ha hx hp1) (prodP hd he ho2 hq (fun _ => hp) hp2))
    (catP (colP (PolyT.mul (PolyT.const 2) hd) hp2 hr hp1 hc1)
      (catP (colP (PolyT.add hd (PolyT.const 1)) hr hb hs hc2)
        (colP (PolyT.add hd (PolyT.const 1)) hz hcp hs hc3)))
end DetDLP.S8M.EffCombinators


