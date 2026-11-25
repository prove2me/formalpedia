-- Prove2me | Definitions.Def_DetDLP_S8L_SubPoly
-- name    : DetDLP_S8L_SubPoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T13:01:13.33208+00:00
-- url     : https://prove2.me/theorems/5121b9bd-87e3-42c4-af9b-f87821dadc29
-- title:
--   Polynomial packet subroutines
-- statement:
--   Explicit polynomial-time address and size certificates for atom, stage, and repeated base codes.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_PacketCode
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
namespace DetDLP.S8L.MakePacket
open S8H0 RegisterMap NamedBlocks GateSemantics S8H.PointAddresses S8C Groundwork M89S1 S8G.FpAtomRows
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.div PolyT.mod PolyT.length w4_M5Evaluator.clog2_poly w4_M5Evaluator.vertexCount_poly w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly
attribute [local fun_prop] wiresP P2M_Groundwork_PolyT_ite__226169acf219 PolyT.decide_lt PolyT.decide_eq
private theorem repP {α : Type} [Enc α] {K : α → ℕ} {F : α → ℕ → NC} (hk : PolyT K) (hf : ∀ {J : α → ℕ}, PolyT J → Eff (fun x => F x (J x))) : Eff (fun x => repeated (K x) (F x)) := by
  have z := hf (PolyT.const (0:ℕ)); refine ⟨PolyT.mul hk z.1,PolyT.mul hk z.2.1,fun hi => ?_⟩
  have q := PolyT.div hi z.2.1; have r := PolyT.mod hi z.2.1
  exact ⟨PolyT.add (PolyT.mul q z.1) ((z.2.2 r).1),((hf q).2.2 r).2⟩
private abbrev FP {α : Type} [Enc α] (F : α → ℕ → ℕ) := ∀ {J : α → ℕ}, PolyT J → PolyT fun x => F x (J x)
private theorem rowP {α : Type} [Enc α] {N M : α → ℕ} {F : α → ℕ → ℕ → ℕ} (hn : PolyT N) (hm : PolyT M) (hf : ∀ {J K : α → ℕ}, PolyT J → PolyT K → PolyT fun x => F x (J x) (K x)) : Eff (fun x => rowN (N x) (M x) (F x)) := ⟨hn,PolyT.mul hn hm,fun hi => ⟨PolyT.div hi hm,hf (PolyT.div hi hm) (PolyT.mod hi hm)⟩⟩
private theorem colP {α : Type} [Enc α] {N : α → ℕ} {A B Z C : α → ℕ → ℕ} (hn : PolyT N) (ha : FP A) (hb : FP B) (hz : FP Z) (hc : FP C) : Eff (fun x => colN (N x) (A x) (B x) (Z x) (C x)) := by
  have U := add_poly id (by intros; assumption)
  refine ⟨hn,PolyT.mul hn (PolyT.const 5),fun {I} hi => ⟨PolyT.div hi (PolyT.const 5),?_⟩⟩
  have hk : PolyT fun x => (S8H.PointAddresses.add (N x)).bit (I x) := U.bit hn hi
  have hj := PolyT.div hk (PolyT.const 4); have hr := PolyT.mod hk (PolyT.const 4)
  exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hr (PolyT.const 0)) (ha hj) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hr (PolyT.const 1)) (hb hj) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hr (PolyT.const 2)) (hz hj) (hc hj)))
private theorem prodP {α : Type} [Enc α] {D E O : α → ℕ} {A B Z : α → ℕ → ℕ} (hd : PolyT D) (he : PolyT E) (ho : PolyT O) (ha : FP A) (hb : FP B) (hz : FP Z) : Eff (fun x => prodN (D x) (E x) (O x) (A x) (B x) (Z x)) := by
  unfold prodN; refine catP ⟨mul_poly.ng hd,mul_poly.ne hd,fun hi => ⟨mul_poly.gate hd hi,?_⟩⟩ (rowP (PolyT.mul (PolyT.const 4) hd) (PolyT.const 2) ?_)
  · exact PolyT.add ho (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hi he) hi (PolyT.sub hi he))
  · intro J K hj hk
    have hh := PolyT.mul (PolyT.const 2) hd
    exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hk (PolyT.const 0)) (PolyT.add ho (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hh) hj (PolyT.add (PolyT.sub he hh) (PolyT.sub hj hh)))) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hd) (ha hj) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hh) (hb (PolyT.sub hj hd)) (hz (PolyT.sub hj hh))))
private theorem wdP {α : Type} [Enc α] {O N P J : α → ℕ} (ho : PolyT O) (hn : PolyT N) (hp : PolyT P) (hj : PolyT J) : PolyT fun x => wd (O x) (N x) (P x) (J x) := P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hn) (PolyT.add ho hj) hp
private theorem rangeP {α : Type} [Enc α] {D P O : α → ℕ} (hd : PolyT D) (hp : PolyT P) (ho : PolyT O) : Eff (fun x => rangeN (D x) (P x) (O x)) := colP (PolyT.add hd (PolyT.const 1)) (fun h => wdP ho hd hp h) (fun h => wdP (PolyT.add ho hd) hd hp h) (fun _ => hp) (fun h => PolyT.add (PolyT.add ho (PolyT.mul (PolyT.const 2) hd)) h)
private theorem asP {α : Type} [Enc α] {D E : α → ℕ} (hd : PolyT D) (he : PolyT E) : PolyT fun x => (Routes.atom (D x) (E x)).size := by
  have H (d e : ℕ) : (Routes.atom d e).size = 24*d+2*e+8 := by simp only [Routes.atom,Routes.extra,RegisterMap.triple,run,RegisterMap.mul,GateRoutes.auxShape,Shape.size]; omega
  simp only [H]; exact PolyT.add (PolyT.add (PolyT.mul (PolyT.const 24) hd) (PolyT.mul (PolyT.const 2) he)) (PolyT.const 8)
private theorem ssP {α : Type} [Enc α] {D E : α → ℕ} (hd : PolyT D) (he : PolyT E) : PolyT fun x => (stageShape (D x) (E x)).size := by
  have H (d e : ℕ) : (stageShape d e).size = 7*d+2*e := by simp only [stageShape,Shape.size]; omega
  simp only [H]; exact PolyT.add (PolyT.mul (PolyT.const 7) hd) (PolyT.mul (PolyT.const 2) he)
private theorem regsP {α : Type} [Enc α] {M D E : α → ℕ} (hm : PolyT M) (hd : PolyT D) (he : PolyT E) : PolyT fun x => regs (M x) (D x) (E x) := by
  have h := PolyT.mul (PolyT.const 2) hm
  have ht := PolyT.add hd (PolyT.add hd (PolyT.add hd (PolyT.const 1)))
  exact PolyT.add (PolyT.mul h (asP hd he)) (PolyT.add (PolyT.mul (PolyT.sub h (PolyT.const 1)) (ssP hd he)) (PolyT.mul (PolyT.sub h (PolyT.const 2)) ht))
private theorem intermP {α : Type} [Enc α] {M D E J : α → ℕ} (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hj : PolyT J) : PolyT fun x => interm (M x) (D x) (E x) (J x) := by
  have h := PolyT.mul (PolyT.const 2) hm
  have ht := PolyT.add hd (PolyT.add hd (PolyT.add hd (PolyT.const 1)))
  exact PolyT.add (PolyT.add (PolyT.mul h (asP hd he)) (PolyT.mul (PolyT.sub h (PolyT.const 1)) (ssP hd he))) (PolyT.mul hj ht)
private theorem atomP {α : Type} [Enc α] {M D E J : α → ℕ} (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hj : PolyT J) : Eff (fun x => atomN (M x) (D x) (E x) (J x)) := by
  have hpin := (regsP hm hd he)
  have hsize := (asP hd he)
  have htr := (PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1))
  have ho := (PolyT.mul hj hsize)
  have ht := (PolyT.add (PolyT.add ho htr) (PolyT.mul (PolyT.const 2) hd))
  have hz := (PolyT.add ht htr)
  have hr := (PolyT.add hz htr)
  have hq := (PolyT.add hr htr)
  have ha := (PolyT.add hq hd)
  have hb := (PolyT.add (PolyT.add ha (PolyT.mul (PolyT.const 2) hd)) he)
  have hcp := (PolyT.add (PolyT.add hb (PolyT.mul (PolyT.const 2) hd)) he)
  have haux := (PolyT.add hcp (PolyT.const 1))
  exact (catP (catP (catP (prodP hd he (PolyT.add ha (PolyT.mul (PolyT.const 2) hd)) (fun h => hpin) (fun h => (wdP ho hd hpin h)) (fun h => (wdP ha (PolyT.mul (PolyT.const 2) hd) hpin h))) (prodP hd he (PolyT.add hb (PolyT.mul (PolyT.const 2) hd)) (fun h => (wdP hq hd hpin h)) (fun h => hpin) (fun h => (wdP hb (PolyT.mul (PolyT.const 2) hd) hpin h)))) (catP (colP (PolyT.mul (PolyT.const 2) hd) (fun h => (wdP hb (PolyT.mul (PolyT.const 2) hd) hpin h)) (fun h => (wdP hr hd hpin h)) (fun h => (wdP ha (PolyT.mul (PolyT.const 2) hd) hpin h)) (fun h => (PolyT.add haux h))) (catP (colP (PolyT.add hd (PolyT.const 1)) (fun h => (wdP hr hd hpin h)) (fun h => hpin) (fun h => (wdP (PolyT.add haux (PolyT.mul (PolyT.const 2) hd)) (PolyT.add hd (PolyT.const 1)) hpin h)) (fun h => (PolyT.add (PolyT.add (PolyT.add haux (PolyT.mul (PolyT.const 3) hd)) (PolyT.const 1)) h))) (colP (PolyT.add hd (PolyT.const 1)) (fun h => (wdP hz hd hpin h)) (fun h => hcp) (fun h => (wdP (PolyT.add haux (PolyT.mul (PolyT.const 2) hd)) (PolyT.add hd (PolyT.const 1)) hpin h)) (fun h => (PolyT.add (PolyT.add (PolyT.add haux (PolyT.mul (PolyT.const 4) hd)) (PolyT.const 2)) h)))))) (catP (rangeP hd hpin ho) (catP (colP hd (fun h => (PolyT.add (PolyT.add ho htr) h)) (fun h => hpin) (fun h => (wdP ho hd hpin h)) (fun h => (PolyT.add (PolyT.add (PolyT.add ho htr) hd) h))) (catP (rangeP hd hpin hz) (catP (rangeP hd hpin hr) (catP (rangeP hd hpin ht) (rowP hd (PolyT.const 2) (fun j k => (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq k (PolyT.const 0)) (PolyT.add hz j) (PolyT.add ht j))))))))))
private theorem stageP {α : Type} [Enc α] {M D E J : α → ℕ} (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hj : PolyT J) : Eff (fun x => stageN (M x) (D x) (E x) (J x)) := by
  have hpin := (regsP hm hd he)
  have hsize := (asP hd he)
  have hs := (PolyT.add (PolyT.mul (PolyT.mul (PolyT.const 2) hm) hsize) (PolyT.mul hj (ssP hd he)))
  have ha := (PolyT.add hs hd)
  have hb := (PolyT.add (PolyT.add ha (PolyT.mul (PolyT.const 2) hd)) he)
  exact (catP (catP (prodP hd he (PolyT.add ha (PolyT.mul (PolyT.const 2) hd)) (fun h => (wdP (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hj (PolyT.const 0)) (PolyT.const 0) (intermP hm hd he (PolyT.sub hj (PolyT.const 1)))) hd hpin h)) (fun h => (wdP (PolyT.mul (PolyT.add hj (PolyT.const 1)) hsize) hd hpin h)) (fun h => (wdP ha (PolyT.mul (PolyT.const 2) hd) hpin h))) (prodP hd he (PolyT.add hb (PolyT.mul (PolyT.const 2) hd)) (fun h => (wdP hs hd hpin h)) (fun h => hpin) (fun h => (wdP hb (PolyT.mul (PolyT.const 2) hd) hpin h)))) (colP (PolyT.mul (PolyT.const 2) hd) (fun h => (wdP hb (PolyT.mul (PolyT.const 2) hd) hpin h)) (fun h => (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj (PolyT.sub (PolyT.mul (PolyT.const 2) hm) (PolyT.const 2))) (wdP (intermP hm hd he hj) hd hpin h) hpin)) (fun h => (wdP ha (PolyT.mul (PolyT.const 2) hd) hpin h)) (fun h => (PolyT.add (PolyT.add (PolyT.add hb (PolyT.mul (PolyT.const 2) hd)) he) h))))
private theorem anchorP {α : Type} [Enc α] {K : α → ℕ} {F : α → ℕ → ℕ} (hk : PolyT K) (hf : FP F) : Eff (fun x => (AnchoredLayout.anchorCode (K x),F x)) := ⟨hk,hk,fun hi => ⟨hi,hf hi⟩⟩
theorem baseP {α : Type} [Enc α] {M D E L : α → ℕ} (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hl : PolyT L) : Eff (fun x => base (M x) (D x) (E x) (L x)) := by
  have hpin := (regsP hm hd he)
  have hsize := (asP hd he)
  exact (catP (anchorP (PolyT.add hpin (PolyT.const 1)) (fun h => h)) (catP (anchorP (PolyT.const 1) (fun h => hpin)) (catP (repP (PolyT.mul (PolyT.const 2) hm) (fun h => (atomP hm hd he h))) (catP (repP (PolyT.sub (PolyT.mul (PolyT.const 2) hm) (PolyT.const 1)) (fun h => (stageP hm hd he h))) (catP (repP (PolyT.sub (PolyT.mul (PolyT.const 2) hm) (PolyT.const 2)) (fun h => (rangeP hd hpin (intermP hm hd he h)))) (catP (rowP (PolyT.const 1) (PolyT.const 0) (fun _ _ => PolyT.const 0)) (rowP hl (PolyT.const 1) (fun j _ => (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt (PolyT.div (PolyT.div j (PolyT.sub hd (PolyT.const 1))) (PolyT.const 2)) hm) (wdP (PolyT.mul (PolyT.add (PolyT.div (PolyT.div j (PolyT.sub hd (PolyT.const 1))) (PolyT.const 2)) (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq (PolyT.mod (PolyT.div j (PolyT.sub hd (PolyT.const 1))) (PolyT.const 2)) (PolyT.const 0)) (PolyT.const 0) hm)) hsize) hd hpin (PolyT.sub (PolyT.sub (PolyT.sub hd (PolyT.const 1)) (PolyT.const 1)) (PolyT.mod j (PolyT.sub hd (PolyT.const 1))))) hpin)))))))))
end DetDLP.S8L.MakePacket


