-- Prove2me | Definitions.Def_DetDLP_S8G_TileEff
-- name    : DetDLP_S8G_TileEff
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T02:25:18.171907+00:00
-- url     : https://prove2.me/theorems/bdddc803-571b-5da5-9b2a-4d0e58dbc670
-- title:
--   Polynomial-time seed and atom tiles
-- statement:
--   Proves polynomial-time construction of seed, scan, check and atom components.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_PacketCode_v2
import Definitions.Def_DetDLP_S8M_EffCombinators

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork FpAtomRows ResidueWires
open DetDLP.S8M.EffCombinators

@[simp] theorem seedSlot_size (d : ℕ) : (seedSlot d).size = 8*d+3 := by simp [seedSlot, triple, Shape.size]; omega
@[simp] theorem stageShape_size (d e : ℕ) : (stageShape d e).size = 7*d+2*e := by simp [stageShape, Shape.size]; omega
@[simp] theorem triple_size (d : ℕ) : (triple d).size = 3*d+1 := by simp [triple, Shape.size]; omega
@[simp] theorem atomSlot_size (d e : ℕ) : (atomSlot d e).size = 22*d+2*e+8 := by simp [atomSlot, triple, run, auxShape, RegisterMap.mul, Shape.size]; omega
@[simp] theorem chainShape_size (n d e : ℕ) : (chainShape n d e).size = n*(7*d+2*e) + (n-1)*(3*d+1) := by simp [chainShape, stageShape_size, triple_size, Shape.size]

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const PolyT.mul PolyT.div PolyT.mod PolyT.sub PolyT.length
  w4_M5Evaluator.clog2_poly w4_M5Evaluator.vertexCount_poly w4_M5EdgeNat.srcNat_poly w4_M5EdgeNat.dstNat_poly
attribute [local fun_prop] wiresP P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 PolyT.decide_lt PolyT.decide_eq

theorem anchorP {α : Type} [Enc α] {N : α → ℕ} {F : α → ℕ → ℕ} (hn : PolyT N) (hf : FP F) :
    Eff (fun x => anchorN (N x) (F x)) := ⟨hn, hn, fun hi => ⟨hi, hf hi⟩⟩

theorem scanP {α : Type} [Enc α] {N C : α → ℕ} {X T : α → ℕ → ℕ} (hn : PolyT N) (hx : FP X) (ht : FP T) (hc : PolyT C) :
    Eff (fun x => scanN (N x) (X x) (T x) (C x)) := by
  refine ⟨PolyT.add hn (PolyT.const 1), PolyT.add (PolyT.mul (PolyT.const 3) hn) (PolyT.const 1), fun hi => ⟨PolyT.div hi (PolyT.const 3), ?_⟩⟩
  have q := PolyT.div hi (PolyT.const 3); have r := PolyT.mod hi (PolyT.const 3)
  exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq r (PolyT.const 0))
    (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq q (PolyT.const 0)) hc (ht (PolyT.sub q (PolyT.const 1))))
    (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq r (PolyT.const 1)) (hx q) (ht q))

theorem allP {α : Type} [Enc α] {N : α → ℕ} {F : α → ℕ → NC} (hn : PolyT N) (hu : Unary fun x => N x - 1)
    (hf : Eff fun z : α × ℕ => F z.1 z.2) : Eff (fun x => allN (N x) (F x)) := by
  have hm := manyN_poly hu hf; have hz := PolyT.decide_eq hn (PolyT.const 0)
  refine ⟨?_, ?_, fun hi => ⟨?_, ?_⟩⟩
  · exact (P2M_Groundwork_PolyT_ite__226169acf219 hz (PolyT.const 0) hm.1).congr fun x => by dsimp only [allN]; split_ifs <;> rfl
  · exact (P2M_Groundwork_PolyT_ite__226169acf219 hz (PolyT.const 0) hm.2.1).congr fun x => by dsimp only [allN]; split_ifs <;> rfl
  · exact (P2M_Groundwork_PolyT_ite__226169acf219 hz (PolyT.div hi (PolyT.const 0)) (hm.2.2 hi).1).congr fun x => by dsimp only [allN]; split_ifs <;> rfl
  · exact (P2M_Groundwork_PolyT_ite__226169acf219 hz (PolyT.const 0) (hm.2.2 hi).2).congr fun x => by dsimp only [allN]; split_ifs <;> rfl

theorem busP {α : Type} [Enc α] {N P O : α → ℕ} (hn : PolyT N) (hp : PolyT P) (ho : PolyT O) : FP (fun x => bus (N x) (P x) (O x)) :=
  fun hj => P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hj hn) (PolyT.add ho hj) hp

theorem checkP {α : Type} [Enc α] {D P X Y C : α → ℕ} (hd : PolyT D) (hp : PolyT P) (hx : PolyT X) (hy : PolyT Y) (hc : PolyT C) :
    Eff (fun x => checkN (D x) (P x) (X x) (Y x) (C x)) :=
  colP (PolyT.add hd (PolyT.const 1)) (busP hd hp hx) (busP hd hp hy) (fun _ => hp) (fun hj => PolyT.add hc hj)

theorem seedP {α : Type} [Enc α] {M D P L : α → ℕ} (hm : PolyT M) (hu : Unary fun x => M x - 1) (hd : PolyT D) (hp : PolyT P) (hl : PolyT L) :
    Eff (fun x => seedN (M x) (D x) (P x) (L x)) := by
  unfold seedN; simp only [triple_size, seedSlot_size]
  refine catP (allP hm hu ?_) (rowP hl (PolyT.const 1) ?_)
  · have pi := PolyT.fst (PolyT.id' (α := α × ℕ))
    have d' : PolyT (fun z : α × ℕ => D z.1) := PolyT.comp hd pi; have p' : PolyT (fun z : α × ℕ => P z.1) := PolyT.comp hp pi
    have hi : PolyT (fun z : α × ℕ => z.2) := PolyT.snd PolyT.id'
    have ht := PolyT.add (PolyT.mul (PolyT.const 3) d') (PolyT.const 1)
    have ho := PolyT.mul hi (PolyT.add (PolyT.mul (PolyT.const 8) d') (PolyT.const 3))
    have hd2 := PolyT.mul (PolyT.const 2) d'
    have ho1 := PolyT.add ho ht
    have ho2 := PolyT.add ho (PolyT.mul (PolyT.const 2) ht)
    exact catP (checkP d' p' ho (PolyT.add ho d') (PolyT.add ho hd2))
      (catP (checkP d' p' ho1 (PolyT.add ho1 d') (PolyT.add ho1 hd2))
        (colP (PolyT.add d' (PolyT.const 1)) (busP d' p' ho) (fun _ => p') (busP d' p' ho2)
          (fun hj => PolyT.add (PolyT.add ho2 d') hj)))
  · intro I K hI _
    have hb := PolyT.sub hd (PolyT.const 1)
    have ho := PolyT.mul (PolyT.div (PolyT.div hI hb) (PolyT.const 2)) (PolyT.add (PolyT.mul (PolyT.const 8) hd) (PolyT.const 3))
    have ht := PolyT.add (PolyT.mul (PolyT.const 3) hd) (PolyT.const 1)
    exact P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_lt hI (PolyT.mul (PolyT.mul hm (PolyT.const 2)) hb))
      (PolyT.add (P2M_Groundwork_PolyT_ite__226169acf219 (PolyT.decide_eq (PolyT.mod (PolyT.div hI hb) (PolyT.const 2)) (PolyT.const 0))
        (PolyT.add ho (PolyT.mul (PolyT.const 2) ht)) (PolyT.add ho ht))
        (PolyT.sub (PolyT.sub hb (PolyT.const 1)) (PolyT.mod hI hb)))
      hp

theorem atomP {α : Type} [Enc α] {D E P O A B : α → ℕ} (hd : PolyT D) (he : PolyT E) (hp : PolyT P) (ho : PolyT O) (ha : PolyT A) (hb : PolyT B) :
    Eff (fun x => atomN (D x) (E x) (P x) (O x) (A x) (B x)) := by
  unfold atomN; simp only [triple_size]
  refine catP (checkP hd hp ?_ ?_ ?_) (catP (scanP hd (busP hd hp ?_) ?_ hp) (catP (checkP hd hp ?_ ?_ ?_) (catP (checkP hd hp ?_ ?_ ?_) (catP (checkP hd hp ?_ ?_ ?_)
    (genHashP hd he ?_ ?_ hp (busP hd hp ha) (busP hd hp ho) (busP hd hp hb) (busP hd hp ?_) (busP hd hp ?_) (busP hd hp ?_) (busP (PolyT.mul (PolyT.const 2) hd) hp ?_) (busP (PolyT.mul (PolyT.const 2) hd) hp ?_) (busP (PolyT.add hd (PolyT.const 1)) hp ?_) ?_ ?_ ?_ ?_)))))
  all_goals (try (unfold FP; intros)); fun_prop (disch := assumption)

end DetDLP.S8G.MakePacketV2


