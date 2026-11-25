-- Prove2me | Definitions.Def_DetDLP_S8L_FpPairGraph
-- name    : DetDLP_S8L_FpPairGraph
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:54:36.043659+00:00
-- url     : https://prove2.me/theorems/aa5325d7-4782-4059-aea6-7cbed1eadfc4
-- title:
--   Graph bounds and counting interface for the finite-field pair query
-- statement:
--   For tag 5 the seed, target and prefix fit the linear block budget. A layout decoding to shortened checked pair transcripts gives the prescribed pair count; the graph and port budgets suffice using the explicit scale and a uniform constant.

import Definitions.Def_DetDLP_S8G_FpMomentGraph

import Definitions.Def_DetDLP_S8L_FpPairChain
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
namespace DetDLP.S8L.FpPair
open M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

variable {p : ℕ} [Fact p.Prime] 

def word {m : ℕ} (T : ℕ) (S : FpSeed p m) (X : (ZMod p)ˣ) (η : List Bool) :=
  queryWord 5 (countWord p) [countWord T,List.ofFn (fpBits S),countWord (X : ZMod p).val,η]

theorem wordLen {m T : ℕ} (S : FpSeed p m) (X : (ZMod p)ˣ) (η : List Bool) (hm : 1 ≤ m)
    (hT : T ≤ p) (hη : η.length ≤ 2*m*bitLen p) :
    (word T S X η).length ≤ 256*m*bitLen p := by
  have hb : 1 ≤ bitLen p := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hc := S8G.FpMoment.binaryLen (le_refl p)
  have hx := S8G.FpMoment.binaryLen (ZMod.val_lt (X : ZMod p)).le
  have ht := S8G.FpMoment.binaryLen hT
  have h6 : (countWord 5).length = 3 := by decide
  have h1 := Nat.le_mul_of_pos_left (bitLen p) hm
  have h2 := Nat.le_mul_of_pos_right m hb
  simp only [word,queryWord,Encoding.encodeList,id_eq,List.length_cons,List.length_append,w3_frameLength,List.length_nil,List.length_ofFn,h6]
  ring_nf at hη ⊢
  omega

def scale (m b : ℕ) := 524288*m*(b+2)

theorem degreeBudget {m b : ℕ} (hm : 1 ≤ m) :
    max 12 (Nat.ceil (136*((b:ℝ)+2)^((3:ℝ)/4))) ≤ Nat.ceil ((scale m b:ℝ)^((9:ℝ)/10)) := by
  apply (S8G.FpMoment.degreeBudget hm).trans
  apply Nat.ceil_mono; apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact_mod_cast (show S8G.FpMoment.scale m b ≤ scale m b by unfold scale S8G.FpMoment.scale; gcongr <;> norm_num)

noncomputable def value {m : ℕ} (T : ℕ) (S : FpSeed p m) (X : (ZMod p)ˣ) (η : List Bool) :=
  pairCount (fpFactorBlock T S) S8C.elemWord (fun ab => (∏ i, ab.1 i * ab.2 i) = X) η

variable {T : ℕ} (S : FpSeed p (blockCount (bitLen p))) (X : (ZMod p)ˣ) (η : List Bool)

theorem wordBudget (hT : T ≤ p) (hη : η.length ≤ 2*blockCount (bitLen p)*bitLen p) :
    let b := bitLen p; let m := blockCount b; let w := word T S X η
    scale m b+w.length ≤ 1600000*m*b ∧ scale m b+w.length ≤ 1600000*(b+1)^1600000 := by
  dsimp only; let b := bitLen p; let m := blockCount b
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hb : 1 ≤ b := Nat.clog_pos (by decide) (Fact.out : p.Prime).one_lt
  have hw := wordLen S X η hm hT hη
  have hs : scale m b ≤ 1572864*m*b := by
    calc _ ≤ 524288*m*(3*b) := Nat.mul_le_mul_left _ (by omega)
         _ = _ := by ring
  have hfirst : scale m b+(word T S X η).length ≤ 1600000*m*b := by nlinarith
  refine ⟨hfirst,hfirst.trans ?_⟩
  rw [Nat.mul_assoc]; apply Nat.mul_le_mul_left
  calc m*b ≤ (b+2)*b := Nat.mul_le_mul_right b (S8G.FpMoment.blockUpper b)
       _ ≤ (b+1)^2 := by nlinarith
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)

theorem ofLayout (hT : T ≤ p) (hη : η.length ≤ 2*blockCount (bitLen p)*bitLen p)
    (A : w3_FactorLayout) (test : w3_factorTest A) (hg : Function.Surjective A.gate)
    (make port : List Bool → List Bool) 
    (witness : {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃
      {v : S8C.UnitPair p (blockCount (bitLen p)) × S8C.PairRun p (blockCount (bitLen p)) // shortOK S T X η v.1 v.2})
    (edges : 2*A.ne < scale (blockCount (bitLen p)) (bitLen p))
    (degree : ∀ v, (w3_factorGraph A).deg v ≤ max 12 (Nat.ceil (136*((bitLen p:ℝ)+2)^((3:ℝ)/4))))
    (build : make (word T S X η) = encodeBTNInstance (word T S X η) (w3_factorGraph A).subdivision
      (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
    (eval : ∀ v a, port (encodePortQuery (word T S X η) v.val (List.ofFn a)) =
      encodeNatListBin [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a then 1 else 0]) :
    S8C.Realizes make port 1600000 (word T S X η) (bitLen p) (value T S X η) := by
  let b := bitLen p; let m := blockCount b; let s := scale m b; let w := word T S X η
  have hm : 1 ≤ m := (by decide : 1 ≤ 2).trans (le_max_left _ _)
  have hscale : b+2 ≤ s := Nat.le_mul_of_pos_left _ (by dsimp [m] at hm; dsimp [m]; positivity)
  have hs : 2 ≤ s := by omega
  have he : 2*A.ne < s := edges
  have dims := w3_incDims A hg
  have qs := w3_incQueryBounds A hg s (by omega) he.le w
  have wb := wordBudget S X η hT hη
  change S8C.Realizes _ _ _ _ _ (value T S X η)
  rw [show value T S X η = Fintype.card ↥(S8C.pairSet S T X η) from (S8C.pairSet_card ..).symm]
  refine S8C.wireRealizes make port 1600000 s b w _ _ (((w3_factorEquiv A test).trans witness).trans (shortEquiv w3_m5_modmul_r2 S T X η)) hs
    (by omega) edges ?_ ?_ wb.1 wb.2 build ?_
  · change A.ng+A.nb+A.ne ≤ s^1600000
    calc _ ≤ s^2 := by nlinarith [dims.1,dims.2]
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  · apply (max_le (Finset.sup_le (fun v _ => degree v)) (le_trans (by decide : 2 ≤ 12) (le_max_left _ _))).trans
    exact degreeBudget hm
  · intro v a
    refine ⟨(Nat.le_of_succ_le (qs.2 v a)).trans ?_,eval v a⟩
    exact (Nat.pow_le_pow_right (by omega) (by decide : 5 ≤ 1600000)).trans
      (Nat.le_mul_of_pos_left _ (by decide))

theorem tagIntro (make port : List Bool → List Bool) (L : ℕ) (hm : Groundwork.PolyT make)
    (he : Groundwork.PolyT port)
    (h : ∀ (p : ℕ) [Fact p.Prime]
      (T : ℕ) (S : FpSeed p (blockCount (bitLen p))) (X : (ZMod p)ˣ) (η : List Bool), T ≤ p →
      η.length ≤ 2*blockCount (bitLen p)*bitLen p →
      S8C.Realizes make port L (word T S X η) (bitLen p) (value T S X η)) :
    S8C.TagSpec [5] := by
  refine ⟨make,port,L,hm,he,?_⟩
  rintro t ht base payload b n hq
  obtain rfl : t = 5 := by simpa using ht
  generalize hw : queryWord 5 base payload = w at hq ⊢
  have tag : Groundwork.PolyT.bval (DetDLP_W1_Queries.first w) = 5 := by subst w; simp [queryWord]
  cases hq <;> simp only [queryWord,DetDLP_W1_Queries.first_cons,id_eq,DetDLP_W1_Queries.decode_count] at tag
  all_goals first | contradiction | exact h _ _ _ _ _ (by assumption) (by assumption)

end DetDLP.S8L.FpPair


