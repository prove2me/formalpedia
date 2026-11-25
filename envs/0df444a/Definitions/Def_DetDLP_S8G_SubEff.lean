-- Prove2me | Definitions.Def_DetDLP_S8G_SubEff
-- name    : DetDLP_S8G_SubEff
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:02:32.435815+00:00
-- url     : https://prove2.me/theorems/5f2c9288-440f-5364-a1e1-a07c74dc768a

import Definitions.Def_DetDLP_S8G_TileEff
import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork FpAtomRows ResidueWires
open DetDLP.S8M.EffCombinators

private abbrev c (k : ℕ) {α : Type} [Enc α] : PolyT (fun _ : α => k) := PolyT.const k
private abbrev iteP {α : Type} [Enc α] {p : α → Bool} {a b : α → ℕ}
    (hp : PolyT fun x => decide (p x = true)) (ha : PolyT a) (hb : PolyT b) :
    PolyT (fun x => if p x then a x else b x) :=
  P2M_Groundwork_PolyT_ite__226169acf219 hp ha hb

attribute [local irreducible] catN rowN colN prodN allN checkN bus seedN atomN anchorN Eff

theorem chainP {α : Type} [Enc α] {M D E P R B A : α → ℕ}
    (hm : PolyT M) (hu1 : Unary fun x => M x - 1 - 1 - 1) (hu2 : Unary fun x => M x - 1 - 1)
    (hd : PolyT D) (he : PolyT E) (hp : PolyT P) (hr : PolyT R) (hb : PolyT B) (ha : PolyT A) :
    Eff (fun x => chainN (M x) (D x) (E x) (P x) (R x) (B x) (A x)) := by
  unfold chainN; simp only [stageShape_size, triple_size, atomSlot_size]
  have hn := PolyT.sub hm (c 1)
  have hlen := P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hn (c 0)) hd (c 0)
  refine catP (rowP hlen (c 2) ?_) (catP (allP (PolyT.sub hn (c 1)) hu1 ?_) (allP hn hu2 ?_))
  · intro I K hI hK
    exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hK (c 0)) (busP hd hp ha hI) (busP hd hp hr hI)
  · have pi := PolyT.fst (PolyT.id' (α := α × ℕ)); have hi := PolyT.snd (PolyT.id' (α := α × ℕ))
    have d' := PolyT.comp hd pi; have e' := PolyT.comp he pi; have p' := PolyT.comp hp pi
    have b' := PolyT.comp hb pi; have n' := PolyT.sub (PolyT.comp hm pi) (c 1)
    have w' := PolyT.add (PolyT.mul (c 7) d') (PolyT.mul (c 2) e')
    have t' := PolyT.add (PolyT.mul (c 3) d') (c 1)
    have tmp' := PolyT.add b' (PolyT.mul n' w')
    have o' := PolyT.add tmp' (PolyT.mul hi t')
    exact checkP d' p' o' (PolyT.add o' d') (PolyT.add o' (PolyT.mul (c 2) d'))
  · have pi := PolyT.fst (PolyT.id' (α := α × ℕ)); have hi := PolyT.snd (PolyT.id' (α := α × ℕ))
    have d' := PolyT.comp hd pi; have e' := PolyT.comp he pi; have p' := PolyT.comp hp pi
    have b' := PolyT.comp hb pi; have a' := PolyT.comp ha pi; have r' := PolyT.comp hr pi
    have n' := PolyT.sub (PolyT.comp hm pi) (c 1)
    have d2 := PolyT.mul (c 2) d'
    have w' := PolyT.add (PolyT.mul (c 7) d') (PolyT.mul (c 2) e')
    have t' := PolyT.add (PolyT.mul (c 3) d') (c 1)
    have aw' := PolyT.add (PolyT.add (PolyT.mul (c 22) d') (PolyT.mul (c 2) e')) (c 8)
    have tmp' := PolyT.add b' (PolyT.mul n' w')
    have o' := PolyT.add b' (PolyT.mul hi w')
    have l' := PolyT.add o' d'
    have k' := PolyT.add (PolyT.add l' d2) e'
    have x' := P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hi (c 0)) a'
      (PolyT.add tmp' (PolyT.mul (PolyT.sub hi (c 1)) t'))
    have z' := P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hi (PolyT.sub n' (c 1)))
      (PolyT.add tmp' (PolyT.mul hi t')) r'
    have ay' := PolyT.add a' (PolyT.mul (PolyT.add hi (c 1)) aw')
    exact catP (catP (prodP d' e' (PolyT.add l' d2) (busP d' p' x') (busP d' p' ay') (busP d2 p' l'))
      (prodP d' e' (PolyT.add k' d2) (busP d' p' o') (fun _ => p') (busP d2 p' k')))
      (colP d2 (busP d2 p' k') (busP d' p' z') (busP d2 p' l') (fun hj => PolyT.add (PolyT.add (PolyT.add k' d2) e') hj))

attribute [local irreducible] chainN

private def treeAux (m d e c v L t s a w o r pin : ℕ) :=
  catN (anchorN (pin+1) id) (catN (anchorN 1 (fun _ => pin)) (catN (seedN m d pin L) (catN (allN c fun k => allN m fun i => atomN d e pin (o+k*(m*a)+i*a) (i*s+2*t) (i*s+t))
    (allN v fun j => let z := r+j*(t+c*w); catN (checkN d pin z (z+d) (z+2*d)) (allN c fun k => chainN m d e pin z (z+t+k*w) (o+k*(m*a)))))))

private theorem treeAuxP {α : Type} [Enc α] {M D E C V L T0 S0 A0 W0 O0 R0 P0 : α → ℕ}
    (hm : PolyT M) (hum : Unary fun x => M x - 1) (hu1 : Unary fun x => M x - 1 - 1 - 1) (hu2 : Unary fun x => M x - 1 - 1)
    (hd : PolyT D) (he : PolyT E) (hc : PolyT C) (huc : Unary fun x => C x - 1) (hv : PolyT V) (huv : Unary fun x => V x - 1) (hl : PolyT L)
    (ht0 : PolyT T0) (hs0 : PolyT S0) (ha0 : PolyT A0) (hw0 : PolyT W0) (ho0 : PolyT O0) (hr0 : PolyT R0) (hpin0 : PolyT P0) :
    Eff (fun x => treeAux (M x) (D x) (E x) (C x) (V x) (L x) (T0 x) (S0 x) (A0 x) (W0 x) (O0 x) (R0 x) (P0 x)) := by
  unfold treeAux
  refine catP (anchorP (PolyT.add hpin0 (c 1)) fun hj => hj) (catP (anchorP (c 1) fun _ => hpin0) (catP (seedP hm hum hd hpin0 hl) (catP ?_ ?_)))
  · have pi1 := PolyT.fst (PolyT.id' (α := α × ℕ))
    apply allP hc huc
    apply allP (PolyT.comp hm pi1) (PolyT.comp hum pi1)
    have pi2 := PolyT.comp pi1 (PolyT.fst (PolyT.id' (α := (α × ℕ) × ℕ)))
    have hk := PolyT.comp (PolyT.snd PolyT.id') (PolyT.fst (PolyT.id' (α := (α × ℕ) × ℕ)))
    have hi := PolyT.snd (PolyT.id' (α := (α × ℕ) × ℕ))
    have ma := PolyT.mul (PolyT.comp hm pi2) (PolyT.comp ha0 pi2)
    have off := PolyT.add (PolyT.add (PolyT.comp ho0 pi2) (PolyT.mul hk ma)) (PolyT.mul hi (PolyT.comp ha0 pi2))
    have is0 := PolyT.mul hi (PolyT.comp hs0 pi2)
    have t2 := PolyT.comp ht0 pi2
    exact atomP (PolyT.comp hd pi2) (PolyT.comp he pi2) (PolyT.comp hpin0 pi2) off
      (PolyT.add is0 (PolyT.mul (c 2) t2)) (PolyT.add is0 t2)
  · have pi1 := PolyT.fst (PolyT.id' (α := α × ℕ))
    have hj := PolyT.snd (PolyT.id' (α := α × ℕ))
    apply allP hv huv
    have d1 := PolyT.comp hd pi1; have p1 := PolyT.comp hpin0 pi1; have t1 := PolyT.comp ht0 pi1
    have cw1 := PolyT.mul (PolyT.comp hc pi1) (PolyT.comp hw0 pi1)
    have z1 := PolyT.add (PolyT.comp hr0 pi1) (PolyT.mul hj (PolyT.add t1 cw1))
    refine catP (checkP d1 p1 z1 (PolyT.add z1 d1) (PolyT.add z1 (PolyT.mul (c 2) d1))) ?_
    apply allP (PolyT.comp hc pi1) (PolyT.comp huc pi1)
    have pi1' := PolyT.fst (PolyT.id' (α := (α × ℕ) × ℕ))
    have pi2 := PolyT.comp pi1 pi1'
    have hk := PolyT.snd (PolyT.id' (α := (α × ℕ) × ℕ))
    have z2 := PolyT.comp z1 pi1'
    exact chainP (PolyT.comp hm pi2) (PolyT.comp hu1 pi2) (PolyT.comp hu2 pi2)
      (PolyT.comp hd pi2) (PolyT.comp he pi2) (PolyT.comp hpin0 pi2) z2
      (PolyT.add (PolyT.add z2 (PolyT.comp ht0 pi2)) (PolyT.mul hk (PolyT.comp hw0 pi2)))
      (PolyT.add (PolyT.comp ho0 pi2) (PolyT.mul hk (PolyT.mul (PolyT.comp hm pi2) (PolyT.comp ha0 pi2))))

private theorem tree_eq_aux (m d e c v L : ℕ) :
    tree m d e c v L =
      let t := 3 * d + 1; let s := 8 * d + 3; let a := 22 * d + 2 * e + 8
      let w := (m - 1) * (7 * d + 2 * e) + (m - 1 - 1) * (3 * d + 1)
      let o := m * s; let r := o + c * (m * a)
      treeAux m d e c v L t s a w o r (o + (c * (m * a) + v * (t + c * w))) := by
  unfold tree treeAux; simp only [triple_size, seedSlot_size, atomSlot_size, chainShape_size]

theorem treeP {α : Type} [Enc α] {M D E C V L : α → ℕ}
    (hm : PolyT M) (hum : Unary fun x => M x - 1) (hu1 : Unary fun x => M x - 1 - 1 - 1) (hu2 : Unary fun x => M x - 1 - 1)
    (hd : PolyT D) (he : PolyT E) (hc : PolyT C) (huc : Unary fun x => C x - 1) (hv : PolyT V) (huv : Unary fun x => V x - 1) (hl : PolyT L) :
    Eff (fun x => tree (M x) (D x) (E x) (C x) (V x) (L x)) := by
  simp only [tree_eq_aux]
  have t0 := PolyT.add (PolyT.mul (c 3) hd) (c 1)
  have s0 := PolyT.add (PolyT.mul (c 8) hd) (c 3)
  have a0 := PolyT.add (PolyT.add (PolyT.mul (c 22) hd) (PolyT.mul (c 2) he)) (c 8)
  have n0 := PolyT.sub hm (c 1)
  have w0 := PolyT.add (PolyT.mul n0 (PolyT.add (PolyT.mul (c 7) hd) (PolyT.mul (c 2) he))) (PolyT.mul (PolyT.sub n0 (c 1)) t0)
  have o0 := PolyT.mul hm s0
  have r0 := PolyT.add o0 (PolyT.mul hc (PolyT.mul hm a0))
  have pin0 := PolyT.add o0 (PolyT.add (PolyT.mul hc (PolyT.mul hm a0)) (PolyT.mul hv (PolyT.add t0 (PolyT.mul hc w0))))
  exact treeAuxP hm hum hu1 hu2 hd he hc huc hv huv hl t0 s0 a0 w0 o0 r0 pin0

attribute [local irreducible] tree

private theorem smallU {α : Type} [Enc α] {q : α → ℕ} {bound : α → List Unit} (hq : PolyT q) (hb : PolyT bound) (hle : ∀ x, q x ≤ (bound x).length) : Unary q :=
  (PolyT.unary_min_length hq hb).congr fun x => by simp only [min_eq_left (hle x)]

theorem gen_networkCode_eff {α : Type} [Enc α] {W : α → PacketWord} (hw : PolyT W) : Eff (fun x => networkCode (W x)) := by
  unfold networkCode
  have hp := PolyT.comp prime_poly hw; have hb := width_poly hp; have hd := PolyT.add hb (c 1); have hm := slots_poly hb
  have hi := PolyT.comp idx_poly hw; have hl := PolyT.length (PolyT.comp prefix_poly hw)
  have hc : PolyT fun x => min (idx (W x)) 2 := (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hi (c 2)) hi (c 2)).congr fun x => by simp [min_def]; split_ifs <;> omega
  have hv : PolyT fun x => if idx (W x) = 3 then 1 else 0 := P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq hi (c 3)) (c 1) (c 0)
  let pad (x : α) := ((prime (W x) - 1).bits ++ [false,false,false,false]).map (fun _ => ())
  have hpad : PolyT pad := PolyT.map (PolyT.const ()) (PolyT.append (PolyT.bits (PolyT.sub hp (c 1))) (PolyT.const _))
  have hm_le (x : α) : slots (width (prime (W x))) ≤ (pad x).length := by
    have h1 : (pad x).length = bitLen (prime (W x)) + 4 := by
      have hw' := width_eq (prime (W x)); simp only [width] at hw'
      simp [pad, ← hw']
    have h2 := FpMoment.blockUpper (bitLen (prime (W x)))
    rw [h1, slots_eq, width_eq]; omega
  have hum := smallU (PolyT.sub hm (c 1)) hpad fun x => (Nat.sub_le _ _).trans (hm_le x)
  have hu2 := smallU (PolyT.sub (PolyT.sub hm (c 1)) (c 1)) hpad fun x => (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (hm_le x))
  have hu1 := smallU (PolyT.sub (PolyT.sub (PolyT.sub hm (c 1)) (c 1)) (c 1)) hpad fun x => (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (hm_le x)))
  have huc := smallU (PolyT.sub hc (c 1)) (PolyT.const [(), ()]) fun x => by simp
  have huv := smallU (PolyT.sub hv (c 1)) (PolyT.const [()]) fun x => by simp; split_ifs <;> omega
  exact treeP hm hum hu1 hu2 hd (wiresP hd) hc huc hv huv hl

theorem networkCode_eff : Eff networkCode := gen_networkCode_eff PolyT.id'
theorem networkCode_idx_eff : Eff (fun z : PacketWord × ℕ => networkCode z.1) := gen_networkCode_eff (PolyT.fst PolyT.id')

end DetDLP.S8G.MakePacketV2


