-- Prove2me | Definitions.Def_DetDLP_S8M_StepBaseNat
-- name    : DetDLP_S8M_StepBaseNat
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:45:35.203997+00:00
-- url     : https://prove2.me/theorems/a7d89e3a-0f01-4574-b84e-5e4230edaf04

import Definitions.Def_DetDLP_S8M_StepBaseDefs
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.StepBaseNat
open S8H0 RegisterMap S8H.MakeCombinators EffCombinators AtomMapNat Groundwork S8N.ECAddRoutes

attribute [local fun_prop] PolyT.const PolyT.add PolyT.mul PolyT.sub PolyT.mod PolyT.div PolyT.decide_eq PolyT.decide_lt wdP P2M_Groundwork_PolyT_ite__226169acf219
variable {α : Type} [Enc α] {M D E I P U V O : α → ℕ}

theorem hashP {Z A0 : α → ℕ} {A X B : α → ℕ → ℕ} (hd : PolyT D) (he : PolyT E)
    (hp : PolyT P) (hz : PolyT Z) (hu : PolyT A0) (ha : FP A) (hx : FP X) (hb : FP B) :
    Eff fun x => hashN (D x) (E x) (P x) (Z x) (A0 x) (A x) (X x) (B x) := by
  unfold hashN; apply genHashP <;> first | assumption | (intro J hj; fun_prop) | fun_prop

private theorem operandP (hd : PolyT D) (he : PolyT E) (hp : PolyT P) (hu : PolyT U) (hv : PolyT V) (ho : PolyT O) (k : ℕ) :
    FP fun x => operand (D x) (E x) (P x) (U x) (V x) (O x) k := by
  intro J hj; simp only [operand]; split_ifs <;> fun_prop

attribute [local irreducible] catN rangeN manyN hashN rowN repeated operand tags Eff
private theorem tileHashP (hd : PolyT D) (he : PolyT E) (hp : PolyT P) (hu : PolyT U) (hv : PolyT V) (ho : PolyT O) (g : ℕ) :
    Eff fun x =>
      let tr := 3 * D x + 1; let l := O x + 1 + 4 * tr + 2; let z := l + D x + g * (16 * D x + 2 * E x + 6)
      hashN (D x) (E x) (P x) z (z + 11 * D x + 2 * E x + 3)
        (operand (D x) (E x) (P x) (U x) (V x) (O x) (tags g).1)
        (operand (D x) (E x) (P x) (U x) (V x) (O x) (tags g).2.1)
        (operand (D x) (E x) (P x) (U x) (V x) (O x) (tags g).2.2) :=
  hashP hd he hp (by fun_prop) (by fun_prop) (operandP hd he hp hu hv ho _) (operandP hd he hp hu hv ho _) (operandP hd he hp hu hv ho _)

private theorem tileP (hd : PolyT D) (he : PolyT E) (hp : PolyT P) (hu : PolyT U) (hv : PolyT V) (ho : PolyT O) :
    Eff fun x => tile (D x) (E x) (P x) (U x) (V x) (O x) := by
  simp only [tile]
  refine catP (manyN_const_poly 3 _ fun _ => rangeP hd hp (by fun_prop))
    (catP (manyN_const_poly 14 _ fun _ => catP (rangeP hd hp (by fun_prop)) (rangeP hd hp (by fun_prop)))
      (catP (manyN_const_poly 14 _ fun g => tileHashP hd he hp hu hv ho g) ?_))
  repeat' first | apply catP | apply rowP
  all_goals first | (intro J K hj hk; fun_prop) | fun_prop

theorem stepN_eff (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hi : PolyT I) :
    Eff fun x => stepN (M x) (D x) (E x) (I x) := by
  simp only [stepN,addOff,mapOff,add_size,slot_size,map_size,bank_size]; apply tileP <;> fun_prop

theorem foldN_eff (hm : PolyT M) (hd : PolyT D) (he : PolyT E) : Eff fun x => foldN (M x) (D x) (E x) := by
  simp only [foldN,addOff,mapOff,add_size,slot_size,map_size,bank_size]
  repeat' first | apply catP | apply rowP | (apply repP; case hf => intro J hj; exact stepN_eff hm hd he hj)
  all_goals first | (intro J K hj hk; fun_prop) | fun_prop

private theorem anchorP {N : α → ℕ} {F : α → ℕ → ℕ} (hn : PolyT N) (hf : FP F) : Eff fun x => anchorN (N x) (F x) := by
  unfold Eff; exact ⟨hn,hn,fun hi => ⟨hi,hf hi⟩⟩

theorem baseN_eff {B L : α → ℕ} (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hb : PolyT B) (hl : PolyT L) :
    Eff fun x => baseN (M x) (D x) (E x) (B x) (L x) := by
  simp only [baseN,digit,bank_size,slot_size]
  refine catP (anchorP (by fun_prop) (fun h => h)) (catP (anchorP (PolyT.const _) (by intro J hj; fun_prop)) ?_)
  refine catP (repP (by fun_prop) (fun h => atomN_eff hm hd he h)) (catP (repP (by fun_prop) (fun h => mapN_eff hm hd he h)) ?_)
  exact catP (foldN_eff hm hd he) (rowP hl (PolyT.const _) (by intro J K hj hk; fun_prop))
end DetDLP.S8M.StepBaseNat


